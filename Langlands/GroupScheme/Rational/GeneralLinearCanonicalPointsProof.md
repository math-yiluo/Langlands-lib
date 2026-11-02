# Canonical rational-point comaps for the block subgroups of GL

This derived interface proof identifies the rational-point carriers of
`GeneralLinear.blockShapeParabolic`, `blockShapeLevi` and
`blockShapeUnipotent` with the inverse images of the Library's concrete matrix
subgroups under precisely the coefficient map used in
`GeneralLinearStandardParabolicStatement`. It works over every commutative ring
`R : CommRingCat`, for every rank `N` and every `B : BlockShape N`, including
ranks zero and one. Specializing `R` to `CommRingCat.of k` gives the target's
arbitrary-field comparisons.

The map is `GeneralLinear.pointsEquiv (Fin N) R` at the identity test scheme
`Over.mk (𝟙 (Spec R))`, followed by
`Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso R).hom.hom`.
`rationalPointsEquiv_toMonoidHom` proves equality of this homomorphism with the
published `rationalPointsEquiv N R`, using `glRingEquiv_eq_map` and the ring
equivalence underlying `Scheme.ΓSpecIso R`.

For each of the three subgroup equalities, the proof first rewrites the block
subgroup functor as the dynamic subgroup for `blockShapeCocharacter B R`.
Subgroup extensionality reduces the assertion to the corresponding published
membership comparison in
`Langlands.GroupScheme.Dynamic.GeneralLinearRationalPoints`:
`mem_parabolic_blockShapeCocharacter_iff`,
`mem_centralizer_blockShapeCocharacter_iff`, or
`mem_unipotent_blockShapeCocharacter_iff`. Thus the inverse-image description
uses the specified canonical homomorphism, without choosing a new isomorphism.

The block conventions come from Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Example 2.1.1, printed
pp. 45–47 (PDF pp. 71–73): decreasing block weights give block upper triangular
parabolics, block diagonal centralizers and unipotent kernels.
Renard, *Représentations des groupes réductifs p-adiques* (2026 French
version), V.3.8, printed p. 111 (PDF p. 117), supplies the standard-parabolic
terminology relative to a fixed minimal parabolic in its nonarchimedean local
field setting. The commutative-ring scope here follows from the published
algebraic matrix construction and coefficient transport. The comap equalities
are derived interface statements, rather than literal statements of either
source; they make no assertion about topology.
