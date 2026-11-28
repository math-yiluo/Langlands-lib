# Galois intertwiners for the middle exterior representation

The definition `exteriorOnChart` takes a local isomorphism from
`SL_(n+1)` to a group `G` over `Spec M → Spec K`. It recovers the
isomorphism after base change to `M`, identifies the pulled-back `SL_(n+1)`
with the special linear group over `M`, and reads the exterior power of the
column representation in that chart. The point formula
`exteriorOnChart_pointMatrix` evaluates the compound matrix of the
determinant-one point in the original chart.

For `n + 1 = 2(m + 1)`, suppose that at an automorphism `σ` the chart
discrepancy acts by conjugation by `P_σ` in the inner case and by
conjugation by `P_σ` after inverse transpose in the outer case.
The middle exterior lift `Q_σ` is the compound of `P_σ` in the inner
case. In the outer case it is that compound multiplied by the wedge Gram
matrix on the right. The wedge similitude identity for a determinant-one
matrix turns inverse transpose into conjugation by this Gram matrix.
Consequently the two chart matrices on the middle exterior power are
related by conjugation by `Q_σ`.

The Galois twist evaluates at the cover point composed with `Spec σ`.
The discrepancy takes this changed chart matrix to the original one.
Thus `Q_σ⁻¹` intertwines the original representation with its twist,
as `middleExterior_intertwines` verifies at the universal scheme point
when the base-changed group is affine.

The wedge identity is derived from the pairing in Knus, Merkurjev, Rost
and Tignol, *The Book of Involutions* (1998), (10.6), printed p. 117.
The outer lift uses the exterior involution and the canonical involution
of (10.28), printed pp. 127–128, with the wedge matrix in the
`MiddleExteriorCocycle` convention. The role of the middle exterior
representation in the Tits algebra calculation is described in §27.B,
printed p. 378.
