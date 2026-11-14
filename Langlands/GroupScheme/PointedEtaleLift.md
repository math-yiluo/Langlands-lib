# Lifting a prescribed fibre point of a smooth group scheme

Worker 648.

This is an internal construction derived from the published
`Langlands.AlgebraicGeometry.pointedEtaleSection` in
`Langlands/AlgebraicGeometry/SmoothPointedEtaleSectionConstruction.lean` and the
published pullback point equivalence `GroupScheme.baseChangeBasePointsEquiv`.
It does not require a new external mathematical input.

For an arbitrary scheme `S`, a group scheme `G` over `S`, a point `s : S`,
and a specified `κ(s)`-point `g₀` of the actual residue fibre of `G`,
`PointedEtaleGroupPointData G s g₀` records an étale morphism `p : U → S`,
a point `b : Spec κ(s) → U` over `s`, an actual `U`-point `g` of `G_U`,
and an exact recovery equation. The equation projects `g` to the original
group `G`, restricts it along `b`, and compares it with the image of `g₀`
under the canonical pullback point equivalence.

If the structure morphism of `G` is smooth, `pointedEtaleGroupPoint`
constructs these data. Its proof first views `g₀` as a map `Spec κ(s) → G`,
applies the published pointed étale section theorem to `G → S`, and then
transfers the resulting section to an actual point of `G_U` by the inverse
pullback point equivalence. The recovery equation follows from the
projection formula for that equivalence and the recovery equation of the
pointed section.

`PointedEtaleGroupPointData.exists_point_over` evaluates `b` at the unique
point of `Spec κ(s)` to show that `s` belongs to the image of `p`.
The base need not be affine, reduced or Noetherian, and no affineness or
reductivity condition on `G` is imposed.
