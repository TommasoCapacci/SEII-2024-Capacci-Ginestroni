//SIGNATURES

sig Email {}

sig Password {}

sig GithubUsername {}

abstract sig User {

email: Email,

password: Password

}

sig Student extends User {

username: one GithubUsername

}

sig Educator extends User {

createsTournament: set Tournament,

createBattle: set Battle

}

enum Bool { True, False }

enum ProgrammingLanguage { Python, Java, C }

enum TournamentState { Subscription, Ongoing, Ended }

enum BattleState { TeamFormation, SubmissionPhase, ConsolidationPhase, Finished }

sig Timestamp {

time: Int

} { time >= 0 }

sig Tournament {

subscriptionDeadline: Timestamp,

var state: TournamentState ,

isManaged: some Educator,

var battles: set Battle,

var participants: set Student -> one Int

}

pred earlierThan [t1, t2: Timestamp] {

int t1.time < int t2.time

}

pred earlierEqual [t1, t2: Timestamp] {

int t1.time <= int t2.time

}

sig Battle {

var state: BattleState ,

var participants: set Team,

registrationDeadline: Timestamp,

submissionDeadline: Timestamp,

minTeamSize: Int,

maxTeamSize: Int,

programmingLanguage: ProgrammingLanguage,

codeKata: CodeKata,

a1Eval: Bool,

a2Eval: Bool,

a3Eval: Bool,

manualEval: Bool

}  {

earlierThan[registrationDeadline,submissionDeadline]

minTeamSize > 0

maxTeamSize >= minTeamSize

}

sig Score {

value: Int

} {

int value >= 0 and int value <= 100

}

sig Submission {

ts: Timestamp,

a1Score: lone Score,

a2Score: lone Score,

a3Score: lone Score,

manualScore: lone Score,

overallScore: one Int,

battle: Battle

}

sig Team {

var submissions: set Submission,

participates: one Battle,

var members: some Student,

var battleScore: one Int,

apiToken: one ApiToken,

inviteCode: one InviteCode

}

sig ApiToken{}

sig InviteCode{}

sig CodeKata {

testCases: some TestCase

}

sig TestCase {

//input: String,

//output: String

}


//INTEGRITY CONSTRAINTS

 // each password is associated to some user ( some registration may have the same password )
fact eachPasswordToSomeUser{
all p : Password | ( some u : User | u. password = p)
}

// each username is associated to a unique student
fact eachGitHubUsernameToOneStudent{
all u : GithubUsername | ( one s : Student | s. username = u)
}

// each ApiToken is associated to a unique team
fact eachApitTokenToOneTeam{
all a : ApiToken | ( one t : Team | t. apiToken= a)
}

// each InviteCode is associated to a unique team
fact eachInviteCodeToOneTeam{
all i : InviteCode | ( one t : Team | t. inviteCode= i)
}

// each email is associated to a unique user 
fact eachEmailToOneUser{
all e : Email| ( one u : User | u. email= e)
}

// each tournament has 1 creator
fact eachTournamentHasOneCreator{
all t : Tournament | ( one e : Educator | t in e.createsTournament )
}

// each battle has 1 creator
fact eachBattleHasOneCreator{
all b : Battle | ( one e : Educator | b in e.createBattle)
}

// each battle belongs to only a tournament
fact eachBattleToOneTournament{
all b: Battle| (one t : Tournament | b in t.battles )
}

// each testcase belongs to only a code kata
fact eachTestCaseToOneCodeKata{
all t: TestCase| (one c : CodeKata| t in c.testCases )
}

// each CodeKata belongs to only a battle
fact eachCodeKataToOneBattle{
all c: CodeKata| (one b : Battle| c in b.codeKata )
}

// each Submission belongs to only a Team
fact eachSubmissionToOneTeam{
all s: Submission| (one t : Team| s in t.submissions )
}

// coherence between “participants” of Battle and “participate” of Team
fact coherenceBetweenParticipantsAndParticipate{
all t: Team, b: Battle | t in b.participants <=> t.participates = b
}

//ADDITIONAL CONSTRAINTS

// each student can subscribe only once to a tournament
fact eachStudentSubscribesMostOnce{
all t:Tournament, s:Student | #t.participants[s] <= 1
}

// tournament creator is also managing the tournament (tournament has at least 1 educator managing it)
fact creatorCanManage{ 
all e: Educator, t:e.createsTournament  | e in t.isManaged 
}

// tournament’s participants scores are the sum of battle scores obtained by the teams the student is a member of in the battles of the same tournament
fun allStudentTeamsInEndedBattles[s:Student]:set Team{
{t:Team | s in t.members and t.participates.state = Finished}
}
fun totalTournamentScore[t: Tournament, s: Student]: Int {
sum te: t.battles.participants&allStudentTeamsInEndedBattles[s] | int te.battleScore
}
fact TournamentParticipantsScoreComputation{ 
all t: Tournament, s: Student | #t.participants[s] = 1 implies t.participants[s] = totalTournamentScore[t,s]
}

// submission's overall score is the sum of all the scores
fact OverallScoreCombinesAutoManualScore {
all s:Submission | int s.overallScore = int s.a1Score.value + int s.a2Score.value + int s.a3Score.value + int s.manualScore.value
}

// battleScore is the overall score of the team’s last submission
fun lastSubmission[t: Team]: one Submission {
  { s: t.submissions | no su: t.submissions - s | earlierThan[su.ts, s.ts] }
}
fact battleScoreCombinesAutoManualScore {
  all t: Team | (no t.submissions and t.battleScore = 0) or (t.battleScore = lastSubmission[t].overallScore)
}

// submission happens after battle’s registration deadline
fact SubmissionAfterRegistration {
all s:Submission | earlierThan[s.ts,s.battle.registrationDeadline]
}

// battle registration deadline comes after tournament subscription deadline
fact RegistrationAfterSubscription {
all b:Battle,to:Tournament | b in to.battles	implies earlierThan[to.subscriptionDeadline,b.registrationDeadline]
}

// Student participates only to battles that belong to tournaments he is enrolled in
fact OnlyBattlesInEnrolledTournament {
all s:Student, te:Team, to:Tournament | (s in te.members and te.participates in to.battles) implies (#to.participants[s] = 1)
}

// a battle can be associated to a tournament only if the tournament is not in registration phase anymore
fact NoBattleInTournamentSubscription {
no t:Tournament | t.state = Subscription and #t.battles > 0
}

// if a tournament is ended, then all its battles must be ended too
fact AllBattleEndedIfTournamentEnded {
	all t:Tournament| t.state = Ended implies (all b: t.battles | b.state = Finished)
}

// if a battle is in teamFormation/submission/consolidation state, then its tournament must be on ongoing state
fact AllBattleEndedIfTournamentEnded {
	all t:Tournament, b:t.battles | b.state != Finished implies (t.state != Ended)
}

// automated scores of the submission are present only if they are enabled in the battle
fact AutomatedScorePresentIfEnabled {
all s:Submission | #s.a1Score = 1 <=> s.battle.a1Eval = True and
			#s.a2Score = 1 <=> s.battle.a2Eval = True and
			#s.a3Score = 1 <=> s.battle.a3Eval = True 
}

// manual score if the submission is present only if its enabled in the battle
fact ManualScorePresentIfEanbled {
all s:Submission | #s.manualScore = 1 <=> s.battle.manualEval = True 
}

// a submission can be associated to a battle only if the battle it’s in the submission/consolidation/ended state 
fact noSubmissionInTeamFormationPhase {
no s:Submission | s.battle.state = TeamFormation
}

// a submission can happen only after the registration deadline and before the battle’s submission deadline
fact SubmissionInSubmissionPhase {
all s:Submission | earlierThan[s.battle.registrationDeadline,s.ts] and earlierThan[s.ts,s.battle.submissionDeadline]
}

// a submission to a battle can occur only if the team is participating to the battle
fact TeamSubmitsOnlyToCorrectBattle {
all t:Team, s:Submission | (s in t.submissions) implies (s.battle = t.participates)
}

// a battle can be created only by educators managing the tournament the battle belongs to
fact BattleCreatedByManager {
all b:Battle, e:Educator, t:Tournament | (b in e.createBattle and b in t.battles) implies (e in t.isManaged)
}

// team members count respects battle’s settings
fact TeamSize {
all t:Team | #t.members >= int t.participates.minTeamSize
		and #t.members <= int t.participates.maxTeamSize
}

// a student can participate to a battle only with 1 team
fact OnlyOneTeamPerBattle {
no t1,t2:Team,s:Student  | t1 != t2 
				   and s in t1.members
				   and s in t2.members
				   and t1.participates = t2.participates
}

// tournament scores initialized to 0 ? (if tournament is not started yet or none of its battles are ended)
fact ZeroInitializedTournamentScores {
all s:Student, to:Tournament, b:Battle | (#to.participants[s] = 1 
						     and (to.state = Subscription or (b in to.battles and b.state != Finished) ) ) implies #to.participants[s] = 0
}

// if a submission comes after another, then its timeliness score should be lower
fact LowerTimelinessScore {
all t:Team, disj s1,s2:Submission  |  (s1 in t.submissions and s2 in t.submissions and earlierThan[s1.ts,s2.ts]) 
						implies 
						s1.a1Score.value > s2.a1Score.value
}

// a student can be enrolled to a tournament at most once
fact NoDoubleEnrollment {
no to:Tournament, s:Student| #to.participants[s] > 1 
}

pred world{
#Team=3
#Tournament=2
#Battle = 3
}
run world  for 6
