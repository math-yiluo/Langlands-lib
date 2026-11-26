# Self-pair gamma orders of cyclic weak inductions from equal-rank equations

`CyclicWeakInductionGammaOrderFromTwistEquationsStatement` derives the unique-place self-pair gamma-order comparison for a supplied cuspidal weak induction. It assumes `EqualRankTwistEngineInputsStatement` in each field and presentation universe pair and the weak base-change identity from weak induction to the full upper arithmetic orbit. The twist input concerns number fields with compact additive adelic quotient and nontrivial unitary additive characters of the adèles trivial on the diagonal field. All four independent field and presentation universes are retained.

`cyclicWeakInductionGammaOrderAtFromTwistEquations` uses the twist inputs at the specified
fields `F` and `E`. The theorem `cyclicWeakInductionGammaOrderFromTwistEquations` specializes
its universally quantified hypotheses to those fields and applies this result.

The proof chooses actual cuspidal contragredients and presentations with irreducible admissible finite components over both fields. Downstairs the pair consists of the supplied realization and its dual. Upstairs it consists of the inducing realization paired with the dual of each of its arithmetic conjugates. Every pair has equal rank. The contragredient transport theorem identifies these upper duals with the conjugates of the dual of the inducing realization. Weak induction carries to the two contragredients. The cofinite projection formula in both orientations supplies the ordinary and reflected Euler identities on the chosen presentations.

The proof applies the two-twist order comparison to these pair setups, using the standard global additive character and the same canonical local component and self-dual measure for all pairs over a given field. At the chosen place, the fibre of upper places is a singleton. The ordinary local pair certificate at the trivial twist belongs to the original first local action paired with the smooth contragredient of the second local action. Finite local genericity identifies the class certificate with the integral gamma factor. Equivalences of the original irreducible local components and contragredient compatibility give the certificates on the presentations in the statement. Their rational spectral germs have the same orders as the factors in the equation comparison.

This uses the cofinite pair comparison and the two-twist method of Henniart and Herb, *Automorphic induction for GL(n) (over local non-archimedean fields)* (1995), Lemma 8.13 and §§8.14–8.17.
