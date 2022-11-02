'reach 0.1'

const [ isFinger, ZERO, ONE, TWO, THREE, FOUR, FIVE ] = makeEnum(6);
const [ isGuess, Zero, One, Two, Three, Four, Five, Six, Seven, Eight, Nine, Ten ] = makeEnum(11);
const [ isResult, B_Wins, DRAW, A_Wins] = makeEnum(3);

const winner = (handA, guessA, handB, guessB) => 
((guessA == guessB) ? DRAW :
((handA + handB) == guessA) ? A_Wins :
((handA + handB) == guessB) ? B_Wins :
DRAW)
       

forall(UInt, handA =>
    forall(UInt, guessA =>
        forall(UInt, handB =>
            forall(UInt, guessB =>
                assert(isResult(winner(handA, guessA, handB, guessB)))))));

const Player = {
    ...hasRandom,
    getFinger: Fun([],UInt),
    getGuess: Fun([],UInt),
    seeResult: Fun([UInt], Null),
    seeOutcome: Fun([UInt],Null),
    informTimeout: Fun([],Null),
}

export const main = Reach.App(()=>{
    const Alice = Participant('Alice',{
        ...Player,
        wager: UInt,
        deadline: UInt,
    })

    const Bob = Participant('Bob',{
        ...Player,
        acceptWager: Fun([UInt],Null),
    })

    init()

    const informTimeout = () =>{
        each([Alice, Bob],()=>{
            interact.informTimeout();
        });
    };

    Alice.only(()=>{
        const amount = declassify(interact.wager);
        const deadline = declassify(interact.deadline);
    })
    Alice.publish(amount,deadline)
        .pay(amount)
    commit()

    
    Bob.only(()=>{
        interact.acceptWager(amount);
    })
    Bob.publish()
        .pay(amount)
        .timeout(relativeTime(deadline),()=>closeTo(Alice, informTimeout));
    

    var outcome = DRAW;
    invariant(balance()==amount * 2 && isResult(outcome))
    while(outcome == DRAW)
    {
        commit();

        Alice.only(()=>{
            const _handA = interact.getFinger();
            const [_commitHandA, _saltHandA] =makeCommitment(interact,_handA); 
            const commitHandA = declassify(_commitHandA);

            const _guessA = interact.getGuess();
            const [_commitGuessA, _saltGuessA] =makeCommitment(interact,_guessA); 
            const commitGuessA = declassify(_commitGuessA);
        })

        Alice.publish(commitHandA, commitGuessA)
            .timeout(relativeTime(deadline),()=> closeTo(Bob, informTimeout));
        commit();

        unknowable(Bob, Alice(_handA,_saltHandA,_guessA,_saltGuessA));
        Bob.only(() => {
            const handB = declassify(interact.getFinger());
            const guessB = declassify(interact.getGuess());
        })

        Bob.publish(handB,guessB)
            .timeout(relativeTime(deadline),()=> closeTo(Alice, informTimeout));
        commit();

        Alice.only(()=>{
            const saltHandA = declassify(_saltHandA);
            const handA = declassify(_handA);
            const saltGuessA = declassify(_saltGuessA);
            const guessA = declassify(_guessA);
        });
    
        Alice.publish(saltHandA, handA, saltGuessA, guessA)
            .timeout(relativeTime(deadline),()=>closeTo(Bob, informTimeout));
        checkCommitment(commitHandA, saltHandA, handA);
        checkCommitment(commitGuessA, saltGuessA, guessA);

        outcome = winner(handA, guessA, handB, guessB);
        continue;

    }

    assert(outcome == A_Wins || outcome == B_Wins);
    transfer(2*amount).to(outcome == A_Wins ? Alice : Bob);
    commit();

    each([Alice,Bob],()=>{
        interact.seeOutcome(outcome)
    })
})