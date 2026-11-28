# Transport of compact orbit lattice normalization

The compact orbit lattice uses a positive polarized Harris action on a
quasi-separated base, with the Harris signature and duality prerequisites,
finite Weil transition compatibility, and the rational comparison for
the profinite integer adeles. It intersects the images of the fixed integral
adelic source span under the Weil-compatible frames in a right orbit. Its
inverse image along a chosen frame is the intersection of the translates
of the source span by the level subgroup.
`harrisCompactFrameLatticeCondition_iff` expresses equality with the full
integral Tate image by comparing membership at the image of every source
vector under the frame.

A supplied isomorphism of the finite étale fibre functors at two points
transports the target of a frame by rational Tate transport. This uses finite
cover fibres at both points, `TorsionFiniteEtaleStatement`, invertibility of
every positive integer on the base, and finiteness and étaleness of the
corresponding roots of unity. Integral and rational transport commute with
rationalization. Choosing a frame in the monodromy-fixed right orbit and
applying this commutation to the source criterion proves
`harrisCompactOrbitLatticeCondition_point`.

For a pointed morphism of quasi-separated bases, integral and rational Tate
base change also commute with rationalization. The frame comparison takes
`DualAbelianBaseChangeNaturalityStatement`, `PolarizationBaseChangeStatement`,
`PositivePullbackDualData` for the actual pulled-back object, and existence
of an ambient adelic frame at the composite point. To compare the
monodromy-fixed right orbits using
`harrisCompactOrbitLatticeCondition_baseChange`, the cover fibres at the
point and its composite must be finite. The comparison also uses
`TorsionFiniteEtaleStatement`, invertibility of every positive integer on
both bases, and finite étale roots of unity on both bases.

`harrisCompactOrbitLatticeCondition_levelDataBaseChange` applies the latter
equivalence to the base-change map on the original Harris level data. The
original level orbit supplies the ambient frame. The comparison uses the
same Hodge level functor and pullback dual data as that map. Under the
stated hypotheses these comparisons apply at every compact open Harris
level, including levels that move the fixed integral source span.
