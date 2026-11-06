# Group actions on colimits over levels satisfying a property

This internal construction repeats the published group action on colimits
over compact open levels (`Langlands.Shimura.LevelColimit`) for presheaves
defined only on the levels satisfying a property `P`. An element `g` again
sends level `K` to the conjugate level `g K g⁻¹`; this needs `P` to be stable
under conjugation. For level-trivial presheaves of modules the colimit is a
smooth representation, functorially. When `P` is moreover downward closed and
holds for some level, the colimit of the restriction of a presheaf on all
levels is identified with its colimit over all levels, compatibly with the
actions, naturally in the presheaf, and as smooth representations.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, lets the level vary under the action of a finite adelic group: after
(3.5) on printed p. 307 for the prime-to-ℓ finite adeles, and in the final
sentence of Proposition 4.10 on printed p. 311 for `GG(A_f^{ℓ,p})` as the
level `K(N)^{ℓ,p}` varies. Shimura varieties and their étale coverings are
often only available for sufficiently small levels, so the system of levels
must be restricted to a class of small levels before the colimit is formed.
This module provides that restricted colimit for an arbitrary property `P`.
The published `Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelIndex` defines
`OrderedSmallLevel` as the subtype `{U : CompactOpenLevel.Ordered G // σ.LevelSufficientlySmall U}`,
which has the same form as `RestrictedOrdered P` below; this module does not
import that module and states nothing about it.

The module constructs no Shimura variety, no specific property of levels, and
no cohomology. It does not prove that transition maps are injective, and it
proves no admissibility, finiteness or Hecke-algebra action. Harris's passages
are motivation only; no statement from them is formalized.

## Inputs

All declarations are in namespace `Langlands.Shimura`. The published module
`Langlands.Shimura.Levels` defines the transporter category
`CompactOpenLevel G` of compact open subgroups of a group `G` with a topology:
an arrow `a : K ⟶ L` is an element `a.element` with
`a.element⁻¹ * k * a.element ∈ L.subgroup` for every `k ∈ K.subgroup`, and
`inclusion h` is the arrow with element `1` for `h : K.subgroup ≤ L.subgroup`.
The published `Langlands.Shimura.LevelColimit` provides the ordered synonym
`Ordered G` with `inclusionFunctor`, `selfArrow`, `inf`, `conjLevel g K`
(the level `g K g⁻¹`), `conjArrow g K : conjLevel g K ⟶ K` with element `g`,
the decomposition `eq_inclusion_comp_conjArrow`, the commutation
`conjArrow_comp_inclusion`, and the colimit `LevelColimit.diagram`,
`LevelColimit.ι`, `LevelColimit.translate`, `LevelColimit.action`,
`LevelColimit.map`, `LevelColimit.functor`, `LevelColimit.IsLevelTrivial`
and `LevelColimit.smoothRep`.

Let `P : ObjectProperty (CompactOpenLevel G)`. Mathlib's full subcategory
`P.FullSubcategory` has objects `K` with `K.obj : CompactOpenLevel G` and
`K.property : P K.obj`, and `P.ι` is its inclusion. Its arrows are arrows of
`CompactOpenLevel G`.

## Levels satisfying `P`

These declarations are in namespace `Langlands.Shimura.CompactOpenLevel`.

- `RestrictedOrdered P` is the subtype `{K : Ordered G // P K}`, with the
  inclusion preorder of subgroups.
- `restrictedInclusion P : RestrictedOrdered P ⥤ P.FullSubcategory` sends
  `K ≤ L` to `inclusion`. `restrictedForget P : RestrictedOrdered P ⥤ Ordered G`
  forgets `P`. `restrictedInclusion_comp_ι` states, by `rfl`, that both routes
  to `CompactOpenLevel G` agree.
- `IsDownwardClosed P` is the class stating `P L → P K` whenever
  `K.subgroup ≤ L.subgroup`.
- `restrictedHom P h` and `restrictedSelfArrow P K k hk` are the arrows of
  `P.FullSubcategory` given by `inclusion h` and by `selfArrow K.obj k hk`.

For a topological group `G`:

- `IsConjStable P` is the class stating `P K → P (conjLevel g K)` for all `g`.
- `restrictedInf P K V` is `inf K.val V`, which satisfies `P` by downward
  closure. Instances state that `RestrictedOrdered P` is directed for `≥`
  under `IsDownwardClosed P`, is nonempty under
  `Nonempty P.FullSubcategory`, and is cofiltered under both.
- `exists_restrictedOrdered_le P V` states that, under these two hypotheses,
  every level `V` contains a level satisfying `P`.
- The instance `restrictedForget_initial` states that, under the same two
  hypotheses, `restrictedForget P` is initial, by Mathlib's
  `Functor.initial_of_exists_of_isCofiltered`.
- Assuming `IsConjStable P`, `restrictedConj P g K` is the level
  `conjLevel g K.obj` satisfying `P`, and
  `restrictedConjArrow P g K : restrictedConj P g K ⟶ K` is `conjArrow g K.obj`
  (`restrictedConj_obj`, `restrictedConjArrow_hom`).
  `eq_restrictedHom_comp_restrictedConjArrow` and
  `restrictedConjArrow_comp_restrictedHom` are the restricted forms of the
  published decomposition and commutation laws.

## The colimit and its group action

These declarations are in namespace
`Langlands.Shimura.RestrictedLevelColimit`. Let `C : Type u` with
`Category.{w} C`, `G : Type v`, and `F : P.FullSubcategoryᵒᵖ ⥤ C`.

- `diagram F : (RestrictedOrdered P)ᵒᵖ ⥤ C` is
  `(restrictedInclusion P).op ⋙ F`; `diagram_map` gives its transition maps.
- `IsLevelTrivial F` states `F.map (restrictedSelfArrow P K k hk).op = 𝟙` for
  every level `K` satisfying `P` and every `k ∈ K`.
  `levelTrivialProperty P C` is this as a property of objects.
  `isLevelTrivial_op_comp T hT E` states that `T.op ⋙ E` is level-trivial
  when `T : P.FullSubcategory ⥤ D` sends every restricted self-arrow to the
  identity. `isLevelTrivial_restrict` states that `P.ι.op ⋙ F` is
  level-trivial for a level-trivial presheaf `F` on all levels.

Assume `[HasColimitsOfShape (RestrictedOrdered P)ᵒᵖ C]`.

- `ι F K` is the colimit inclusion of level `K`; `map_restrictedHom_ι` states
  `F.map (restrictedHom P h).op ≫ ι F K = ι F L`; `hom_ext` is the extension
  principle for maps out of the colimit.

Assume moreover that `G` is a topological group and `IsConjStable P`.

- `translateCocone F g` has level-`K` leg
  `F.map (restrictedConjArrow P g K).op ≫ ι F (restrictedConj P g K)`, with
  naturality `translate_leg_naturality`. `translate F g` is the induced
  endomorphism, characterized by `ι_translate`.
- `map_ι a` states `F.map a.op ≫ ι F K = ι F L ≫ translate F a.hom.element`
  for every arrow `a : K ⟶ L` of `P.FullSubcategory`.
- `translate_one` and `translate_mul`
  (`translate F (g * h) = translate F h ≫ translate F g`) follow from `map_ι`,
  and `action F : Action C G` is the colimit with `ρ g = translate F g`
  (`action_V`, `action_ρ`). No level-triviality is needed for the action.
- `ι_translate_of_mem` states `ι F K ≫ translate F k = ι F K` for a
  level-trivial `F` and `k ∈ K`.
- `map α` is the map of colimits induced by `α : F ⟶ F'`, with `ι_map`,
  `map_id`, `map_comp` and `translate_map`.
- `functor P C : (P.FullSubcategoryᵒᵖ ⥤ C) ⥤ Action C G` sends `F` to
  `action F` (`functor_obj`, `functor_map_hom`), and `functorCompForgetIso P C`
  identifies its composite with the forgetful functor with whiskering by
  `(restrictedInclusion P).op` followed by `colim`.

## Smoothness for presheaves of modules

Let `R : Type t` be a commutative ring and assume
`[HasColimitsOfShape (RestrictedOrdered P)ᵒᵖ (ModuleCat.{w} R)]`, with `G` a
topological group and `IsConjStable P`.

- `isSmooth_action F hF` states that, for a level-trivial
  `F : P.FullSubcategoryᵒᵖ ⥤ ModuleCat.{w} R`, the representation of
  `action F` is smooth. The proof is the quotient argument of the published
  `LevelColimit.isSmooth_action`: each `(ι F K).hom x` is fixed by the open
  subgroup `K`, so the quotient by the smooth vectors vanishes after every
  `ι F K` and hence is zero.
- `translate_ι_apply_of_mem` and `translate_ι_apply` are the elementwise forms
  of `ι_translate_of_mem` and `ι_translate`.
- `exists_ι_apply` states, assuming `IsDownwardClosed P` and
  `Nonempty P.FullSubcategory` but neither conjugation stability nor
  level-triviality, that every vector of the colimit is `(ι F K).hom y` for a
  single level `K` satisfying `P`. Such vectors form a submodule, because the
  intersection of two levels satisfying `P` satisfies `P`, and the same
  quotient argument shows that it is everything.
- `smoothRep F hF : SmoothRep.{t, v, w} R G` is the representation of
  `action F` with smoothness `isSmooth_action F hF`, and `smoothRep_ρ_ι_apply`
  states its action on vectors from level `K`.
- `smoothFunctor P R` is the functor from
  `(levelTrivialProperty P (ModuleCat.{w} R)).FullSubcategory` to
  `SmoothRep.{t, v, w} R G` obtained by lifting
  `functor P (ModuleCat.{w} R) ⋙ Rep.ActionToRep R G`
  (`smoothFunctor_obj_obj`).

## Comparison with colimits over all levels

Assume that `G` is a topological group, `IsDownwardClosed P`,
`Nonempty P.FullSubcategory` and `[HasColimitsOfShape (Ordered G)ᵒᵖ C]`, and
let `F₀ : (CompactOpenLevel G)ᵒᵖ ⥤ C`.

- `colimitRestrictIso F₀` identifies the colimit of `diagram (P.ι.op ⋙ F₀)`
  with `colimit (LevelColimit.diagram F₀)`. It is Mathlib's
  `Functor.Final.colimitIso` for the final functor
  `(restrictedForget P).op`, which is final because `restrictedForget P` is
  initial. `ι_colimitRestrictIso_hom` and `ι_colimitRestrictIso_inv` state
  that it matches `ι (P.ι.op ⋙ F₀) K` with `LevelColimit.ι F₀ K.obj`.
- `map_colimitRestrictIso_hom α` states naturality in `F₀`.

Assume moreover `IsConjStable P`.

- `translate_colimitRestrictIso_hom` states that the comparison intertwines
  `translate (P.ι.op ⋙ F₀) g` with `LevelColimit.translate F₀ g`.
- `actionRestrictIso F₀ : action (P.ι.op ⋙ F₀) ≅ LevelColimit.action F₀` is
  the resulting isomorphism in `Action C G` (`actionRestrictIso_hom_hom`), and
  `functorRestrictIso P C` is the natural isomorphism between whiskering by
  `P.ι.op` followed by `functor P C` and `LevelColimit.functor G C`.
- With `R` as above and also `[HasColimitsOfShape (Ordered G)ᵒᵖ (ModuleCat.{w} R)]`,
  `smoothRepRestrictIso F₀ hF₀` identifies
  `smoothRep (P.ι.op ⋙ F₀) (isLevelTrivial_restrict hF₀)` with the published
  `LevelColimit.smoothRep F₀ hF₀`, for a level-trivial presheaf of modules
  `F₀` on all levels; `smoothRepRestrictIso_hom_ι_apply` is its elementwise
  formula on vectors from level `K`.

## Provenance

The constructions are internal assemblies of Mathlib full subcategories,
colimits, cocones, `Functor.Final.colimitIso`, the initiality criterion for
cofiltered categories, `Action`, `ActionToRep`, full-subcategory lifts and
quotient modules, applied to the published level category and the published
`LevelColimit` constructions. Harris's passages cited above are motivation
only.
