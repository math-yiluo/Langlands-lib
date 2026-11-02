# Renard II.2.5: maps of original-action projector sheaves

This module constructs morphisms and the additive functor for the actual
projector basis sheaf. Its original source is David Renard,
*Représentations des groupes réductifs p-adiques* (French version dated
9 July 2026), II.2.5, printed pp.39–40 / PDF pp.45–46, registered as
`renard-2026-representations-groupes-reductifs-padiques` with SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Those pages and the supplementary 2010 corrections PDF pp.2–3 have been
read directly. The original gives the inverse construction for
nondegenerate modules. Extending its underlying additive construction to every
specified original nonunital module is an internal strengthening: the
construction and all its laws use only the original action, additivity and
intertwining.

Fix the supplied topology on `X : Type u` and
`hX : Langlands.Topology.IsLocallyProfinite X`. The imported
`ProjectorPresheaf` and `ProjectorSheaf` modules provide the canonical
compact-open basis, the exact characteristic fixed subgroups and original
projector restrictions, and the proved intrinsic sheaf condition. For
`M : Type v` and `N : Type w` with their specified original
`NonUnitalModule (PointwiseTestAlgebra.Carrier X)` structures, an original
intertwiner `f` induces the additive map

`valueMap hX f U : Value hX M U →+ Value hX N U`.

It is the underlying additive map of the published
`NonUnitalModuleCorner.restrict (idempotent hX U) f`. In full its function is
`s ↦ ⟨f s.val, map_mem_fixedPart … f s.property⟩`, as stated by
`coe_valueMap`; `valueMap_val` exposes its underlying value. Thus the carrier
is exactly the imported fixed subgroup, and the map is exactly the original
additive map restricted to that subgroup. The proof of fixedness uses the
intertwiner identity at the characteristic test.

`valueMap_naturality` states equality of complete additive maps:

`(valueMap hX f U).comp (restrict hX M h) =
  (restrict hX N h).comp (valueMap hX f V)`

for `h : U.obj ≤ V.obj`. The implemented proof applies subtype extensionality
to `f.map_smul (test hX U) s.val`. The application formula is also exposed.
Identity, composition, zero and addition are equalities of entire additive
maps, proved by extensionality and the defining original-map formulas.
`valueMapAddHom` bundles additivity in `f`. These component constructions and
naturality have independent source and target carrier universes `v` and `w`.

When both carrier types lie in one fixed `Type v`, `rawMap` bundles these
components as an actual natural transformation of the imported contravariant
functors. Naturality follows from `valueMap_naturality`, with the inclusion
reversed by the opposite category. `rawMap_app_hom` and `rawMap_app_val`
recover the component additive map and its value. Its identity, composition,
zero and addition laws follow by natural-transformation and additive-map
extensionality.

`sheafMap` is the actual morphism in `BasisSheaf`: it uses the two published
full-subcategory wrappers around `rawMap`. It requires no additional
property of `f` and uses the already proved intrinsic sheaf condition on
both objects. `sheafMap_app_hom`, `coe_sheafMap_app` and
`sheafMap_app_val` expose its full original-map component formula.
`sheafMap_naturality` states the restriction square. Its identity,
composition, zero and addition laws reduce through the wrappers to the
corresponding `rawMap` laws.

The main definition is the actual functor

`functor hX :
  NonUnitalModuleCat.{u,v} (PointwiseTestAlgebra.Carrier X) ⥤
    BasisSheaf.{u,v} (compactOpenBasis hX)`.

Its object is definitionally `basisSheaf hX M`; its map is definitionally
`sheafMap hX f`. The `functor_additive` instance is proved by
`sheafMap_add`. `functor_map_zero`, `functor_map_add` and
`functor_map_app_val` expose its additive laws and original additive
component values. The value formula explicitly projects the categorical
intertwiner to its original `toAddMonoidHom`.

`nondegenerateFunctor` is definitionally
`nondegenerateInclusion (PointwiseTestAlgebra.Carrier X) ⋙ functor hX`.
This exposes Renard's original nondegenerate specialization. Its additive
instance follows from composition of the published additive inclusion and
`functor`. Its object, map, component value, zero and addition formulas are
also exposed.

All bundled constructions retain the unchanged value universe `v` independent
of `u`. Complete unapplied interface examples check the component map and
naturality at independent `u/v/w`, both bundled functors and additive
instances at independent `u/v`, and both functors in the unequal directions
`u = 0, v = 1` and `u = 1, v = 0`.

The construction assumes no nondegeneracy for the ambient functor, no extra
complex scalar action on the module, no smooth multiplier extension and no
locality or gluing premise on the output. It stays at the underlying
abelian-group basis-sheaf level. Scalar sheaves and their modules,
compact-section recovery, equivalences, stalk comparisons and passage to
all opens remain separate constructions.
