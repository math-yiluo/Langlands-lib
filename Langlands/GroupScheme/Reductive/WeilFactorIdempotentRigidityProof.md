# Normal idempotents of a Weil restriction with almost simple geometric fibres

`Langlands.GroupScheme.weilFactorIdempotentRigidity` proves the published
[`WeilFactorIdempotentRigidityStatement`](WeilFactorIdempotentRigidityStatement.md)
in every universe. It gives the unique idempotent of `B ⊗[A] T` whose factor
projection agrees with the given conjugation-equivariant idempotent on every
`T`-algebra.

The Lean proof supplies two theorems to
`WeilFactor.weilFactorIdempotentRigidity_of_inputs`. The reduction uses
`weilAbelianImageTriviality` to kill the homomorphisms between complementary
factors, whose values commute by conjugation equivariance. This allows the
endomorphism to restrict to the factor cut out by the graph idempotent of
the coefficient map from `B`. The theorem `relativeAlmostSimpleNormalIdempotent`
then gives the unique coefficient idempotent for that factor over `B ⊗[A] T`.
The reduction transfers its quotient-point formulas back along the Weil
restriction point equivalence and uses the same relative uniqueness to
identify any other idempotent with the required formulas.
[`Reduction`](WeilFactorRigidityReduction.md),
[`relative rigidity`](RelativeAlmostSimpleNormalIdempotentProof.md),
[`triviality of commuting images`](WeilAbelianImageTrivialityProof.md)

This composition formalizes the factor rigidity used in the Library's approach
to the uniqueness argument in Brian Conrad, *Reductive group schemes* (2014),
Proposition 6.4.4, pp. 232–233, registered as
`conrad-2014-reductive-group-schemes`. Conrad identifies the individual factors
étale-locally. The Lean reduction uses the graph idempotent to isolate the
factor on the given coefficient algebra.
