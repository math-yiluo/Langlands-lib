# Cocommutativity and torsion in affine Hopf coordinates

Worker 1552, task `f02d1dea-6430-41df-bf80-bd95f132e32f`.

This internal adapter connects the actual-scheme hypotheses of
`RelativeRoot.SmoothCommutativePTorsionVectorEmbeddingStatement` to the algebraic
primitive-generation route for the embedding assertion of CGP B.1.10.
It reuses the published affine Hopf-coordinate comparison, the convolution
point equivalence `Spec.mapMulEquiv`, and the scalar-extension restriction
homomorphism `BorelFieldExtension.res`.

`coordinatePointEquiv` identifies convolution on coordinate algebra maps to any
same-universe commutative `k`-algebra with multiplication on the corresponding
actual scheme points, using the affine coordinate group-scheme isomorphism.

`baseChangePointHom` constructs a group homomorphism from the convolution group
of `L`-algebra maps `L ⊗[k] A → L` to the actual `Spec L` points of `G`.
It composes scalar restriction, the spectrum point equivalence, and the affine
coordinate group-scheme isomorphism. `baseChangePointHom_injective` proves that
this comparison determines the scalar-extended algebra map uniquely.

`hopfAlgebra_isCocomm` transports commutativity of an affine actual group scheme
along its coordinate spectrum isomorphism. The universal pair of
coordinate-algebra-valued points then gives cocommutativity, by the published
`isCocomm_of_commute` criterion. No smoothness or connectedness is needed.

`convPow_algHom_eq_one_of_uniformExponent` proves that every coordinate algebra
map with values in any same-universe commutative base algebra is killed by the
given exponent under convolution. Under `Spec.mapMulEquiv` it is a point on the
relative spectrum of that algebra. Composition with the coordinate isomorphism
identifies its power with the power in the original actual group, where the
all-test exponent hypothesis applies. The coordinate isomorphism reflects the
resulting equality.

For every same-universe field extension `L/k`,
`convPow_baseChange_algHom_eq_one_of_uniformExponent` restricts an `L`-algebra
point of `L ⊗[k] A` to a `k`-algebra point of `A`. The published restriction
homomorphism is injective and preserves convolution powers, so the preceding
exponent result transfers to the scalar extension.
`convPow_baseChange_linearMap_eq_one_of_uniformExponent` then applies the
published compatibility of algebra-hom convolution with its underlying linear
map. These facts hold for any natural-number exponent; no characteristic,
reducedness, connectedness or smoothness premise enters this adapter.

This module does not assert primitive generation or the final vector embedding.
Those require the separate smoothness and primitive-generation descent steps.
