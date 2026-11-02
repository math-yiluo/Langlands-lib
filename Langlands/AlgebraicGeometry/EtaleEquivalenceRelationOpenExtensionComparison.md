# Cartesian comparison of open extensions

This internal helper constructs maps between the actual pushout arrow schemes in
`EtaleEquivalenceRelationOpenExtension`. It supports the pushout step of Stacks
Proposition 70.8.1 (Tag 07SU), in the registered source
`stacks-noetherian-approximation-2026-11-01`. The categorical comparison argument
here is derived from the existing open-extension construction and the pullback
universal property; it does not assert a Noetherian first level.

The setup consists of endpoint-preserving maps `f` and `g` between relations `E`
and `F`, open immersions `ι : E.U → V` and `κ : F.U → W`, and a compatible
map `v : V → W`. `unit_naturality` proves preservation of units using uniqueness
of arrows with given endpoints. `map` applies the pushout universal property.
`unit_map`, `inclusion_map`, `map_t`, and `map_s` give its chart and endpoint
equations.

When the original relation morphism is cartesian,
`diagonal_old_hom_ext` proves uniqueness for a diagonal chart and an old-arrow
chart. `chart_hom_ext` handles all four pairs of charts. `hom_ext` pulls back the
open cover twice to deduce global uniqueness, and `mono_pair` packages this as
monicity of the comparison-source pair. These assertions need only a commuting
square of open immersions.

When that square is a pullback, `chart_exists_lift` constructs a compatible lift
on each lower chart. The diagonal chart lifts by the new unit. The old-arrow
chart lifts first through the square of opens and then through the original
source pullback. `exists_lift` glues the local lifts through the monic
comparison-source pair. `isPullback_source` and `isCartesianHom` state the
resulting source pullback and cartesian morphism of extended relations.

All declarations use schemes in an arbitrary universe `u`. No separation or
affineness hypotheses are used.
