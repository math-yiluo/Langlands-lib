# Degree-preserving binary presentations for inner type A of split rank one

Author: Worker 177.

This internal unit constructs an actual binary norm-one presentation for a
simply connected absolutely almost-simple group of inner type A and split rank
one. It works over any field `K : Type u`, in every characteristic, without a
local-field premise. The group is affine and locally of finite type. Its actual
index `d : TitsIndexData G` satisfies `d.HasInnerTypeA n`: positive absolute rank,
every type-A Cartan entry under a numbering, and trivial full Galois star action.

`DegreePreservingBinaryNormOnePresentation K G n` consists of a published
`BinaryNormOnePresentation K G` together with the equation
`2 * Langlands.CentralSimple.reducedDegree K p.divisionAlgebra = n + 1`.
The underlying presentation stores a finite-dimensional central division
`K`-algebra `D : Type u` and an actual group-scheme isomorphism
`G ≅ CentralSimpleUnits.BinaryRoot.groupScheme K D`, the reduced-norm-one
group of the two-by-two matrix algebra over `D`.

`nonempty_degreePreservingBinaryNormOnePresentation` proves that these data
exist, and `innerTypeARankOnePresentation` chooses them. The theorem
`innerTypeARankOne_degree` retains the same actual model and concludes that
its division degree is positive and `n = 2 * reducedDegree K D - 1`.
All declarations are universe-polymorphic in `u`.

## Implemented proof and provenance

The unconditional published theorem `innerTypeANormOne` gives a central simple
algebra `A`, the equation `reducedDegree K A = n + 1`, and an actual norm-one
presentation of `G`. The published `divisionMatrixPresentation` constructs an
algebra equivalence `A ≃ₐ[K] Matrix (Fin m) (Fin m) D` over a finite-dimensional
central division algebra, with positive matrix size `m`. Its `normOneIso`
transports the group-scheme presentation through this algebra equivalence.

The unconditional published `CentralSimpleUnits.matrixNormOneSplitRank` and
split-rank invariance under that isomorphism give `m - 1 = 1`. Positivity of
`m` then forces `m = 2`. The algebra equivalence preserves the `K`-dimension.
The matrix-dimension formula and the published square-dimension formula for
central simple algebras therefore give
`dim_K A = (2 * reducedDegree K D) * (2 * reducedDegree K D)`.
Taking the natural square root, which defines reduced degree, proves the
retained degree equation. The actual composed group-scheme isomorphism and
the same division algebra give the output data. Reduced-degree positivity
and natural-number arithmetic give the final theorem.

This is a derived composition of published algebra and group-scheme theorems;
it introduces no new literature translation. It extends the earlier
`InnerTypeARankOneReduction` by discharging its two structural premises and
retaining the degree equation that the earlier existential proof discarded.
No local rank-one classification or local Kneser--Tits theorem is used.

## Remaining scope

This unit assumes inner type A. It does not prove the position of the
actual distinguished vertex, so it does not prove `HasRankOneInnerAIndex`
or the full `LocalRankOneTitsIndexStatement`. In particular, odd absolute
rank and an actual binary model are not substituted for the exact marked
subset required by that statement.
