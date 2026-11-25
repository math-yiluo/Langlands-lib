# Reduction of reductive monomorphisms to noetherian bases

This proves the conditional
`ReductiveMonomorphismNoetherianReductionStatement`. Homomorphism descent,
scheme monicity descent and direct-limit reductivity remain explicit premises.

On an affine base with ring `A`, the proof chooses the prime subring
`⊥ : Subalgebra ℤ A`, whose carrier lies in the same universe as `A`.
It is noetherian because it is a finitely generated algebra over the integers.
The simultaneous coefficient-model theorem produces an actual reductive
source, separated finitely presented target and monic homomorphism over a
finitely generated subalgebra of `A` over that prime subring.
That coefficient ring is noetherian by the finite-type theorem.

The locally noetherian closed-immersion premise applies to this model.
The underlying morphism of its group base change is a scheme base change,
so it remains a closed immersion. The model's exact recovery square writes
the original homomorphism as this map composed with isomorphisms, proving
the affine-base case.

For a general base, the proof pulls both groups and their homomorphism to
each affine chart. Reductivity, target separatedness and finite presentation,
and monicity are preserved by base change. The affine-base result applies
there. Pulling the affine cover to the target gives an open cover on which
the original scheme morphism is a closed immersion; locality at the target
then gives closedness globally.

The reverse implication restricts the arbitrary-base assertion to locally
noetherian bases. No DVR case or one of the three descent premises is proved.
