# Transport of smooth induction along equivalences

Author: Worker 195.

This module supplies an internal construction for reusing smooth induction after
changing the inducing representation by an actual equivalence. It imports the
published `Induction/Parabolic` construction unchanged. The source and target
carrier universes are independent.

`Induction.smoothInducedEquiv P e` sends an induced function `f` to `e ∘ f`.
It uses the existing `smoothInducedMap`, so covariance, equivariance and preservation
of smooth vectors are inherited. Its inverse is postcomposition by `e.symm`.
The two inverse laws are checked pointwise. `smoothInducedEquiv_eval` records
the pointwise formula. The companion `smoothInducedMap_injective` proves that
an injective intertwiner induces an injective map, by evaluating at each group
element and using injectivity in the inducing space.

`T.normalizedParabolicInducedEquiv B e` applies this construction to a Levi
equivalence after pullback along `B.leviProjection` and twisting by the canonical
`T.parabolicHalfModulus B`. The supplied topology is exactly `T.topology`.
Its evaluation lemma again identifies the underlying map with postcomposition.
`normalizedParabolicInducedMap_injective` verifies pointwise injectivity for the
existing normalized induction map.

These are derived functorial constructions, not additional representation-theoretic
assumptions. They require neither irreducibility nor admissibility, and do not
assert existence of a cuspidal embedding or tensor decomposition. Their role in
the supercuspidal embedding proof is to transport a separately obtained Levi
embedding to the induction of a separately obtained external tensor product.
