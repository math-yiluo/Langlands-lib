# Ambient maximality of maximal tori in parabolic subgroups

This internal construction retains a supplied torus and its actual inclusion.
Over any field `k`, if `i : P → G` is a parabolic subgroup of a connected
reductive group and `t : T → P` is a maximal torus of `P`, then
`IsMaximalTorus.comp_parabolic` proves that the composite `t ≫ i` is a maximal
torus of `G`. There is no splitness or perfectness assumption on `k` or `T`.

The proof derives the smoothness, affineness and connectedness of `P` from
the supplied parabolic predicate and the published parabolic connectedness
theorem. Over an algebraic closure, `parabolicMaximalTorus` supplies one
torus maximal in `G` and factoring through `P`. Its factor is maximal in `P`
by `IsMaximalTorus.of_comp`. The published
`IsMaximalTorus.comp_of_common_geometric_maximalTorus` then transfers this
common geometric maximality to the original supplied torus and reflects
the conclusion to `k`. In particular, the original torus source is preserved.

For every scheme `S` in any universe, the residue-fibre application gives
`IsFibrewiseMaximalTorus.comp_relativeParabolic`: a torus maximal on every
residue fibre of a relative parabolic is also maximal on every residue fibre
of the reductive ambient group. This is an application of the field result
to the actual pullback inclusions. It does not infer subgroup equality from
fibre equality.

`RelativeLevi.parabolicAmbientMaximalTorus` packages the actual composite
`t ≫ i`, its closedness and its ambient fibrewise maximality. Its value
theorem is definitional. The construction assumes a closed supplied torus
map, the full relative parabolic predicate and reductivity of `G`. Closedness
of `i` is supplied by the published `relativeParabolicClosed` theorem under
these hypotheses. It does
not construct a torus, a cocharacter, a Levi subgroup or a conjugator.

The provenance is internal composition of published Library results:
`Torus.GeometricHomMaximal`, `Absolute.ParabolicMaximalTorusProof`,
`Rational.ParabolicConnectedConjugacy`,
`RelativeLevi.ParabolicSourceGeometry`, `RelativeLevi.ParabolicClosedProof`,
and `Torus.FieldPointMaximality`.
This supplies a maximality transport step for prescribed-torus
presentation and contained-torus uniqueness arguments, without proving
either of those stronger statements.
