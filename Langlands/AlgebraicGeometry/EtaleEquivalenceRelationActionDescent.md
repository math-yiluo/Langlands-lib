# Pullback and eventual descent of action laws

Author: Worker 706.

This internal helper combines the fibre product universal property with
Mathlib's equality descent for locally finite type scheme morphisms.
It is intended for the action descent step in the proof of Stacks Project
Proposition 70.8.1, Tag 07SU, registered as
`stacks-noetherian-approximation-2026-11-01`. The construction does not
assert existence of an approximation system or of a descended prospective
action map.

Fix a cartesian relation morphism `h : E → F` with object map `f`, arrow
map `g`, and an object pullback square with maps `k : P → Q`,
`p : P → E.U`, `q : Q → F.U`. For a prospective action map
`b : F.R ×[F.U] Q → Q` satisfying its target equation, `pullbackMap`
uses that square to lift its image in `Q` together with the target of
the upper arrow. `pullbackMap_comparison` and `pullbackMap_over`
are its two projection identities. `pullbackMap_unique` proves that
these identities determine the lifted map. For an actual action `B`,
`pullbackAction` uses naturality of the unit and associativity expressions
and pullback uniqueness to obtain an actual upper action.
`pullbackAction_isEquivariant` states the comparison identity.

For the eventual results, `I` is a cofiltered category in the same
arbitrary universe as the schemes. The object diagram `D` maps compatibly
to `Q`, and the diagram `C` maps compatibly to the universal composable
action domain over `F,q`. Both diagrams have quasi-compact terms and
affine transition maps, and both supplied cones are limits. The morphism
`q` is locally of finite type.

`exists_laws_at_level` assumes that the unit and universal associativity
equations of a supplied prospective map hold after precomposition from
these limits. It descends each equality by
`Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`, using the target
equation to check that both sides lie over the same base map.
Cofilteredness supplies one later index where both equations hold;
naturality of the two diagram comparisons transports them there.

`exists_action_at_level` additionally supplies, for each index, an upper
relation cartesian over `F`, an object pullback over `Q`, and an
identification of its universal composable domain with the corresponding
term of `C`. The identification must intertwine the comparison map with
the map on composable triples. The theorem applies the preceding eventual
equations to one common index and uses `pullbackMap` and
`ofEquationsAfterMap` to construct an action there. The resulting map
is compatible with the prospective lower map. No action laws for that
lower map are assumed.
