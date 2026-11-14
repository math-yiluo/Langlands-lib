# Ordered Čech maps along index maps compute the canonical pullback

Module `Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqPullback`,
namespace `Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq`.

## Purpose

This module computes the Library's canonical cohomology pullback
`relativeCohomologyPullback` and the canonical pushforward comparison
`canonicalPushforwardCohomologyMap` with ordered Čech cochains over all tuples
(module `...CechResolution.AllSeqCohomology`). It works for an arbitrary
morphism and an arbitrary index map between the covers. The index map need not
be monotone or injective. This is possible because ordered cochains are indexed
by all tuples, so composing with the index map is always defined.

The cochain formulas agree with `Langlands.Cohomology.Cech.pull`:
`c ↦ (σ ↦ f.appLE (inter U (α ∘ σ)) (inter V σ) _ (c (α ∘ σ)))`. So the
canonical pullback on structure-sheaf cohomology is the pullback of ordered Čech
cocycles.

## Sheaf-level map (section `Map`)

Let `g : Y ⟶ X` be a morphism of schemes and `a : M ⟶ g_* N`. Let
`U : ι → X.Opens` and `V : κ → Y.Opens` be finite families, and `α : κ → ι` an
index map with `hα : ∀ j, V j ≤ g⁻¹ U (α j)`.

- `preimage_inter`: `g⁻¹ (inter U σ) = ⨅ a, g⁻¹ U (σ a)`.
- `inter_le_preimage`: `inter V τ ≤ g⁻¹ (inter U (α ∘ τ))`.
- `termMap g a α hα p : term U M p ⟶ g_* (term V N p)` has `τ`-component
  `π_{α ∘ τ} ≫ sheafOnPushforward g a _` (`termMap_π`). Here
  `sheafOnPushforward` is the Library's factor map
  `sheafOn M W ⟶ g_* sheafOn N W'` from `CechResolution.BaseChange`. The
  pushforward preserves the finite biproduct, so its limit cone defines the
  map.
- `termMap_d`: the degreewise maps commute with the ordered Čech differentials.
  On the components at `t` and face `j`, this is `termMap_π` at `t ∘ j.succAbove`
  together with the Library's `res_sheafOnPushforward`.
- `complexMap g a α hα : complex U M ⟶ g_* (complex V N)` is the resulting map of
  complexes. `complexMap_f` gives its degreewise maps.
- `augmentation_termMap` and `aug_complexMap` give the augmentation square
  `aug U M ≫ complexMap = single₀.map a ≫ mapResolutionAugmentation g_* (aug V N)`.
  They follow from the Library's `unit_sheafOnPushforward`.

## Cohomology (section `Cohomology`)

Now `X Y : Over (Spec R)`, `h : Y ⟶ X`, `a : M ⟶ h_* N`, and `hU`, `hV` say
that `U` and `V` cover.

- `cochainMap h a U V α hα : cochainComplex X.hom U M ⟶ cochainComplex Y.hom V N`
  is the map induced by `a` and `α`. It is `Γ_X(complexMap)` followed by the
  termwise identification `Γ_X ∘ h_* ≅ Γ_Y`, conjugated by the sections
  isomorphisms.
- `resolutionComparison_comp_canonicalPushforwardCohomologyMap` gives, for every
  `n`,
  `resolutionComparison Γ_X (aug U M) n ≫ H^n(X, a) ≫ canonicalPushforwardCohomologyMap h N n`
  `= H^n(Γ_X(complexMap) ≫ S) ≫ resolutionComparison Γ_Y (aug V N) n`.
  It is the Library theorem
  `DerivedSections.resolutionComparison_comp_canonicalPushforwardCohomologyMap`
  applied to the ordered Čech resolutions, with `aug_complexMap` as the
  compatibility hypothesis.
- `cohomologyIso_comp_canonicalPushforwardCohomologyMap` gives the same identity
  in terms of `cohomologyIso`, for separated `X.hom` and `Y.hom`, quasi-coherent
  `M` and `N`, and affine `U i` and `V j`:
  `(cohomologyIso X.hom U M hU hUa n).hom ≫ H^n(X, a) ≫ canonicalPushforwardCohomologyMap h N n`
  `= homologyMap (cochainMap h a U V α hα) n ≫ (cohomologyIso Y.hom V N hV hVa n).hom`.
- `cohomologyIso_comp_relativeCohomologyPullback` is the case where `a` is the
  pullback–pushforward adjunction unit and `N = h^* M`. It uses the Library's
  `relativeCohomologyPullback_eq_unit_pushforward`.
- `cohomologyIso_comp_relativeCohomologyPullback_coefficient` is the same case
  followed by a coefficient map `b : h^* M ⟶ N`, with `a` the adjoint of `b`. It
  uses the Library's `relativeCohomologyPullback_coefficient`.

## Cochain formulas (section `Elements`)

- `relativePushforwardSectionsIso_hom_app_apply`: the Library identification
  `Γ_X(h_* F) ≅ Γ_Y(F)` is the identity on underlying sections. It reduces to the
  Library's `pushforwardCongr_hom_app_top`.
- `map_map_eq`: two composites of restriction maps between the same opens
  agree.
- `toCochainFun_sectionsComplexIso_inv`: `toCochainFun` inverts the sections
  isomorphism.
- `cochainMap_f_apply`: `(cochainMap h a U V α hα).f p c τ` is
  `N.presheaf.map (homOfLE (inter_le_preimage _ α hα τ)).op (a.app (inter U (α ∘ τ)) (c (α ∘ τ)))`.
  The proof unwinds the sections isomorphisms and `termMap_π` at `τ`. It then
  uses the formula for `sheafOnPushforward` on sections and naturality of `a`
  (`app_map_apply`), and finally `map_map_eq`.
- `cochainMap_unit_f_apply`: for structure sheaves and
  `a = Langlands.Scheme.Modules.unitToPushforwardUnit h.left`, this is
  `h.left.appLE (inter U (α ∘ τ)) (inter V τ) _ (c (α ∘ τ))`.

## Structure sheaf (section `Unit`)

- `homEquiv_pullbackUnitIso_hom`: the adjoint of
  `(Langlands.Scheme.Modules.pullbackUnitIso h.left).hom : h^* 𝒪_X ⟶ 𝒪_Y` is
  `unitToPushforwardUnit h.left`. This is Mathlib's
  `SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`.
- `cohomologyIso_comp_relativeCohomologyPullback_unit` concerns the composite
  `relativeCohomologyPullback h 𝒪_X n ≫ H^n(Y, pullbackUnitIso.hom)` (the form
  used by `FieldH2ExteriorCoproductComparisonStatement`). Under `cohomologyIso`,
  it is `homologyMap` of `cochainMap h (unitToPushforwardUnit h.left) U V α hα`.
  By `cochainMap_unit_f_apply`, that cochain map is the pullback of ordered Čech
  cochains of functions.

## Provenance

This is internal infrastructure. It formalizes the standard fact that the
refinement map of Čech complexes along a map of coverings computes the pullback
on cohomology. The cochain formula is the refinement map of The Stacks Project,
Cohomology of Sheaves, Section "Refinements and Čech cohomology" (tag 09UY),
composed with pullback of sections. This is the same map as the Library's
`Langlands.Cohomology.Cech.pull`. The proof is formal from the Library's
resolution description of the canonical pushforward comparison
(`CohomologyPullbackResolution`) and from the sheaf-level factor maps of
`CechResolution.BaseChange`.
