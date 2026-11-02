# Modules supported at one closed point are skyscrapers

This module proves that an `𝒪_X`-module whose stalks vanish away from a
closed point `x` is the skyscraper module of its stalk at `x`. It extends
the published stalk–skyscraper adjunction in
`Langlands.AlgebraicGeometry.Modules.StalkAdjunction`, and all
declarations live in the namespace
`Langlands.AlgebraicGeometry.Modules.StalkAdjunction`. Throughout, `X` is a
scheme, `x : X` a point, and `N` a module over the local ring
`X.presheaf.stalk x`; `skyscraper x N` is the published skyscraper
`𝒪_X`-module, `stalkFunctor x` the published stalk functor, and
`adjunction x` the published adjunction `stalkFunctor x ⊣ skyscraperFunctor x`.

## Statements

- `subsingleton_sections_of_not_mem x N hx`: for an open `U` with `x ∉ U`,
  the sections of `skyscraper x N` over `U` form a subsingleton.
- `subsingleton_stalk_of_not_specializes x N h`: for a point `y` with
  `¬ x ⤳ y`, the stalk of `skyscraper x N` at `y` is a subsingleton.
- `fromStalkAdd_id_injective x N`: the published evaluation map
  `fromStalkAdd x (𝟙 (skyscraper x N))` from the stalk at `x` of the
  skyscraper to `N` is injective.
- `isIso_unit_app_of_stalkSupport_subset hx M hM`: if `{x}` is closed in
  `X` and the published `stalkSupport M` of a module `M : X.Modules` is
  contained in `{x}`, then the unit `(adjunction x).unit.app M` is an
  isomorphism.
- `isoSkyscraperOfStalkSupportSubset hx M hM`: under the same hypotheses,
  the resulting isomorphism `M ≅ skyscraper x ((stalkFunctor x).obj M)`.
- `germ_bijective_of_stalkSupport_subset hx M hM U hxU`: under the same
  hypotheses, for every open `U` containing `x`, the germ map
  `M.presheaf.germ U x hxU` from sections over `U` to the stalk at `x` is
  bijective.

## Implemented proof

`subsingleton_sections_of_not_mem`: the sections of the skyscraper over `U`
are the published `sections x N U`, functions out of `PLift (x ∈ U)`, which
is empty.

`subsingleton_stalk_of_not_specializes`: by `specializes_iff_forall_open`
there is an open `s` containing `y` but not `x`. Every element of the
stalk at `y` is a germ of a section over some `U ∋ y`; restricting it to
`U ⊓ s`, which does not contain `x`, gives zero by the previous lemma, so
every element is zero.

`fromStalkAdd_id_injective`: an element of the stalk is a germ of a
section `c` over some `U ∋ x`; by the published `fromStalkAdd_germ` its
evaluation is the value of `c` at the proof of `x ∈ U`, so if this is zero
then `c` is zero by function extensionality.

`isIso_unit_app_of_stalkSupport_subset`: the forgetful functor
`SheafOfModules.toSheaf` to sheaves of abelian groups reflects
isomorphisms, so it suffices to check that the underlying morphism of
sheaves of abelian groups is an isomorphism on every stalk
(`TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`), that is, bijective.
At `y = x`, the composite of the stalk map of the unit with the
evaluation `fromStalkAdd x (𝟙 _)` is the identity (checked on germs with
`stalkFunctor_map_germ_apply` and `fromStalkAdd_germ`); together with the
injectivity of the evaluation this gives bijectivity. At `y ≠ x`, the stalk
of `M` is a subsingleton because `y` is outside the stalk support
(`mem_stalkSupport_iff_nontrivial`), and the stalk of the skyscraper is a
subsingleton by the second lemma, since `x` is closed and so does not
specialize to `y`; a map between subsingletons is bijective.

`isoSkyscraperOfStalkSupportSubset` is `asIso` of the unit.

`germ_bijective_of_stalkSupport_subset`: on sections over `U ∋ x`, the germ
map equals the composite of the component of the unit at `U` (an
isomorphism by the previous theorem) with the published
`sectionsIso x _ U hxU` identifying skyscraper sections over `U` with the
stalk; this identity holds definitionally.

## Provenance and scope

The statements are the standard fact that a sheaf supported at a closed
point is the skyscraper of its stalk there. They are internal helpers for
the direct-image half of Edixhoven, van der Geer and Moonen, *Abelian
Varieties* (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), Theorem (9.1) (recognizing `R^g p_* P` as a skyscraper at the origin of the
dual). Closedness of `x` is used only at the points `y ≠ x`.
