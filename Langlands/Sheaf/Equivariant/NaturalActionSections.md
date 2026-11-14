# Sections and invariant sections along a natural action

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.LocalActionCohomology` (imported): for a monoid `K`, an object
  `U` of a category `T` and an action `a : K →* (End U)ᵐᵒᵖ`, the representation
  `actionRepresentation F a` of `K` on the sections `F(U)` of a module presheaf `F`, where `k`
  acts by `F.map (a k).unop.op` (`actionRepresentation_apply`). Also the functor
  `sectionsRep R a : (Tᵒᵖ ⥤ ModuleCat R) ⥤ Rep R K` with `sectionsRepForgetIso a`, and the
  functor `discreteSectionsRep R L J a` on the discrete sheaves of a local action system `L`.
- `Langlands.Sheaf.Equivariant.LocalAction` (through the imports): local action systems
  `LocalActionSystem T G` for a group `G` with a topology, with their admissible actions
  `L.IsAdmissible U H a` of open subgroups `H`, and discrete presheaves `L.IsDiscrete F` (for
  every admissible action, each section is fixed by an open subgroup).
- `Langlands.Sheaf.Equivariant.LocalActionDiscretePart` (through the imports): the category
  `L.DiscreteSheaf A J` of discrete sheaves, its inclusion `discreteSheafInclusion`, and the
  class `L.HasFiniteEquivariantRefinements J`.
- `Langlands.Representation.Category.Basic` (through the imports): `smoothRepProperty R G`
  and `SmoothRep R G`, with `SmoothRep.toRep`.
- Mathlib: `Rep.invariantsFunctor`, `Rep.invariantsAdjunction`, `Rep.ofHom`,
  `LinearMap.intertwiningMap_of_isIntertwiningMap`, `sheafToPresheaf`,
  `preservesFiniteLimits_of_evaluation`, `preservesFiniteLimits_of_reflects_of_preserves`,
  `ObjectProperty.lift` and `ObjectProperty.liftCompιIso`.

All declarations are in the namespace `Langlands.Sheaf.Equivariant`.

## Purpose

Let `Φ : E ⥤ T` be a functor and let a monoid `K` act on every object `Φ V` by
endomorphisms, so that the images under `Φ` of the morphisms of `E` commute with the
actions. Then the sections of a module presheaf `F` on `T` over the objects `Φ V` form a
presheaf on `E` of representations of `K`, and for a group `K` their invariants form a
presheaf of modules `V ↦ F(Φ V)^K` on `E`. These constructions are functorial and left exact
in `F`.

For a `G`-space `X`, take `E = Qét(X(G))` (or `Ét(X(G))`), `T` the twisted quasi-étale (or
étale) site of `X`, and `Φ` the functor that forgets the action of `G` on `V`. Then the
presheaf of invariants is the presheaf `(b_*F)^G : V(G) ↦ F(V)^G` from the proof of
Berkovich's Theorem 1.4.2. That case is `AnalyticInvariantPresheaf`.

## Setting

`T : Type u` with `[Category.{v} T]` and `E : Type uE` with `[Category.{vE} E]`. `R : Type uR`
is a commutative ring and modules live in `ModuleCat.{w} R`.

## Natural actions

- `NaturalAction K Φ`, for a monoid `K` and `Φ : E ⥤ T`: a structure with fields
  `act : ∀ V : E, K →* (End (Φ.obj V))ᵐᵒᵖ` and
  `comm : (act V k).unop ≫ Φ.map f = Φ.map f ≫ (act W k).unop` for every `f : V ⟶ W` and
  `k : K`.
- `NaturalAction.precomp a Ψ`, for `Ψ : E' ⥤ E`: the natural action along `Ψ ⋙ Φ` with
  `act V = a.act (Ψ.obj V)` (`precomp_act`).

## Representations on sections

Let `a : NaturalAction K Φ` and `F : Tᵒᵖ ⥤ ModuleCat.{w} R`.

- `a.sectionsIntertwiningMap R F f`, for `f : V ⟶ W`: the restriction map
  `F.map (Φ.map f).op` as an intertwining map from `actionRepresentation F (a.act W)` to
  `actionRepresentation F (a.act V)` (`sectionsIntertwiningMap_apply`). Proof: both
  composites are `F.map` of the composite arrows, which agree by `a.comm`.
- `a.sectionsRepPresheaf R F : Eᵒᵖ ⥤ Rep.{w} R K`: at `V` the representation
  `(sectionsRep R (a.act V)).obj F`, whose representation is `actionRepresentation F (a.act V)`
  (`sectionsRepPresheaf_obj_ρ`), and on `f` the intertwining map above
  (`sectionsRepPresheaf_map_hom_apply`).
- `a.sectionsRepFunctor R : (Tᵒᵖ ⥤ ModuleCat.{w} R) ⥤ (Eᵒᵖ ⥤ Rep.{w} R K)`, with
  `sectionsRepFunctor_obj`. On a morphism `φ : F ⟶ F'` its component at `V` is
  `(sectionsRep R (a.act V)).map φ`. `sectionsRepFunctor_comp_evaluation`: evaluated at `V` it
  is `sectionsRep R (a.act V)` (an equality, by `rfl`).
- `sectionsRep_preservesFiniteLimits b` (instance): for any action `b` of `K` on an object `U`,
  `sectionsRep R b` preserves finite limits. Proof: followed by the forgetful functor to
  modules it is evaluation at `U` (`sectionsRepForgetIso`), and the forgetful functor
  `Rep R K ⥤ ModuleCat R` preserves and reflects finite limits.
- `sectionsRepFunctor_preservesFiniteLimits` (instance): limits in the functor category are
  computed pointwise (`preservesFiniteLimits_of_evaluation`).
- `a.sheafSectionsRepFunctor R J`, for a Grothendieck topology `J` on `T`: the composite of
  `sheafToPresheaf J` with `a.sectionsRepFunctor R`, and
  `sheafSectionsRepFunctor_preservesFiniteLimits` (instance).

## Invariant sections

Now `K` is a group.

- `a.invariantPresheaf R F : Eᵒᵖ ⥤ ModuleCat.{w} R`: the composite of
  `a.sectionsRepPresheaf R F` with `Rep.invariantsFunctor R K`, the presheaf
  `V ↦ F(Φ V)^K`.
- `mem_invariantPresheaf_obj_iff`: a section `s` over `Φ V` is invariant exactly when
  `F.map (a.act V k).unop.op` fixes it for every `k : K`.
- `invariantPresheaf_map_apply`: restriction of invariant sections along `f` is restriction of
  the underlying sections along `Φ.map f`.
- `a.invariantFunctor R : (Tᵒᵖ ⥤ ModuleCat.{w} R) ⥤ (Eᵒᵖ ⥤ ModuleCat.{w} R)`: the composite
  of `a.sectionsRepFunctor R` with whiskering by `Rep.invariantsFunctor R K`
  (`invariantFunctor_obj`). `invariantFunctor_comp_evaluation`: evaluated at `V` it is
  `sectionsRep R (a.act V) ⋙ Rep.invariantsFunctor R K` (an equality, by `rfl`).
- `invariantFunctor_preservesFiniteLimits` (instance): pointwise, a composite of the left exact
  `sectionsRep R (a.act V)` with `Rep.invariantsFunctor R K`, which preserves limits as a right
  adjoint (`Rep.invariantsAdjunction`).
- `precomp_invariantPresheaf a Ψ F`: the invariant presheaf of `a.precomp Ψ` is
  `Ψ.op ⋙ a.invariantPresheaf R F` (an equality, by `rfl`).
- `a.sheafInvariantFunctor R J`: the composite of `sheafToPresheaf J` with
  `a.invariantFunctor R` (`sheafInvariantFunctor_obj`), and
  `sheafInvariantFunctor_preservesFiniteLimits` (instance).

## Smoothness

Let `G` be a group with a topology, `L : LocalActionSystem T G`, `U : T` and
`b : G →* (End U)ᵐᵒᵖ`. The whole group is the open subgroup `⊤ : OpenSubgroup G`; the
restriction of `b` to it is `b.comp ((⊤ : OpenSubgroup G) : Subgroup G).subtype`. The
hypothesis `hb` below states that this restriction is admissible for `L` on `U`.

- `isSmooth_actionRepresentation_of_isAdmissible_top L hb hF`: if `F` is discrete for `L`
  (`L.IsDiscrete F`), then `actionRepresentation F b` is smooth. Proof: discreteness for the
  admissible action of `⊤` gives, for each section, an open subgroup of `G` whose elements fix
  it under that action, which is the action `b`.
- `discreteSectionsSmoothOfTop R L J hb : L.DiscreteSheaf (ModuleCat.{w} R) J ⥤ SmoothRep R G`:
  the lift of `discreteSectionsRep R L J b` through the full subcategory of smooth
  representations. This differs from the Library's `discreteSectionsSmooth`, which takes an
  admissible action of an open subgroup `H` and gives smooth representations of `H`. Here the
  result is a representation of `G` itself.
- `discreteSectionsSmoothOfTopToRepIso R L J hb`: the underlying representation is
  `discreteSectionsRep R L J b`.
- `discreteSectionsSmoothOfTop_additive` (instance).
- `discreteSectionsSmoothOfTop_preservesFiniteLimits` (instance), assuming
  `[HasSheafify J (ModuleCat.{w} R)]` and `[L.HasFiniteEquivariantRefinements J]`. Proof:
  `discreteSectionsRep R L J b` is left exact (Library instance
  `discreteSectionsRep_preservesFiniteLimits`), and `SmoothRep.toRep` preserves and reflects
  finite limits.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).
Printed page numbers equal PDF page numbers.

- Proof of Theorem 1.4.2, step A.4, printed p.9: "Let now `F` be a quasi-étale `G`-sheaf on
  `X`. For `(V(G) → X(G)) ∈ Qét(X(G))` one has `b_*F(V(G)) = F(V)`. The group `G` acts on
  `F(V)`, and therefore we can define a sheaf `(b_*F)^G` on `X(G)~_qét` by
  `(b_*F)^G(V(G)) = F(V)^G`."

## Provenance

Derived. Berkovich gives the presheaf `(b_*F)^G` only for `G`-spaces. The abstraction to a
natural action along a functor `Φ`, and the smoothness criterion for an admissible action of
the whole group, are ours. They package the parts of that construction that use no geometry.
The sheaf property of the presheaf of invariants is not addressed in this module.
