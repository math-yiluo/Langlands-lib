/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
public import WeilConjectures.CategoryTheory.Abelian.DimensionShifting
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Connecting

/-!
# Cohomology of a pushforward with vanishing higher direct images

Let `π : Y' ⟶ Y` be a morphism of schemes and `ℱ` an `𝒪_{Y'}`-module whose higher direct images
`R^q π_* ℱ` vanish for `q > 0`. Then `H^q(Y, π_* ℱ) ≅ H^q(Y', ℱ)`: this is the degenerate case
of the Leray spectral sequence. We prove it without the spectral sequence, as in
`AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_comp_Γab_iso_functorH`: on the
modules with vanishing higher direct images, both `ℱ ↦ H^q(Y', ℱ)` and `ℱ ↦ H^q(Y, π_* ℱ)` are
effaceable δ-functors (`π_*` is exact on short exact sequences starting with such a module, by
the long exact sequence of the right derived functors of `π_*`), and they agree in degree `0`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.nonempty_functorH_iso_pushforward_of_isZero_higherDirectImage`:
  the natural isomorphism, on the modules with vanishing higher direct images.
- `AlgebraicGeometry.Scheme.Modules.exists_H_addEquiv_pushforward_of_isZero_higherDirectImage`:
  `H^q(Y', ℱ) ≅ H^q(Y, π_* ℱ)`, compatibly with the actions of the global functions on `Y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {Y' Y : Scheme.{u}} (π : Y' ⟶ Y) [HasInjectiveResolutions Y'.Modules]

attribute [local instance] enoughInjectives_of_hasInjectiveResolutions

/-- The `𝒪_{Y'}`-modules whose higher direct images along `π` vanish in all positive degrees. -/
def higherDirectImageAcyclic : ObjectProperty Y'.Modules :=
  fun ℱ ↦ ∀ q : ℕ, IsZero ((higherDirectImage π (q + 1)).obj ℱ)

variable {π}

/-- The pushforward of a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` with `R¹ π_* ℱ₁ = 0` is
short exact: `π_*` is left exact, and `π_* ℱ₂ ⟶ π_* ℱ₃ ⟶ R¹ π_* ℱ₁` is exact. -/
lemma shortExact_map_pushforward_of_isZero {S : ShortComplex Y'.Modules} (hS : S.ShortExact)
    (h : IsZero ((higherDirectImage π 1).obj S.X₁)) : (S.map (pushforward π)).ShortExact := by
  let := HasDerivedCategory.standard Y'.Modules
  let := HasDerivedCategory.standard Y.Modules
  have := (pullbackPushforwardAdjunction π).rightAdjoint_preservesLimits.{0, 0}
  have : PreservesFiniteLimits (pushforward π) := inferInstance
  have := hS.mono_f
  have hepi : Epi ((pushforward π).map S.g) := by
    have h₂ := hS.rightDerivedδ_exact₂ (pushforward π) 0
    have : Epi ((((pushforward π).rightDerived 0).map S.g)) :=
      h₂.epi_f (h.eq_of_tgt _ _)
    have e := ((pushforward π).rightDerivedZeroIsoSelf.hom.naturality S.g)
    have : (pushforward π).map S.g = ((pushforward π).rightDerivedZeroIsoSelf.inv.app S.X₂) ≫
        ((pushforward π).rightDerived 0).map S.g ≫
          (pushforward π).rightDerivedZeroIsoSelf.hom.app S.X₃ := by
      rw [e, Iso.inv_hom_id_app_assoc]
    rw [this]
    infer_instance
  exact ShortComplex.ShortExact.mk' (hS.exact.map_of_mono_of_preservesKernel _ inferInstance
    inferInstance) (Functor.map_mono (pushforward π) S.f) hepi

variable (π) in
/-- The modules with vanishing higher direct images are stable under the dimension shifting
`0 ⟶ ℱ ⟶ I ⟶ Q ⟶ 0`, with `I` the chosen injective object under `ℱ`. -/
lemma higherDirectImageAcyclic_under_cokernel (ℱ : Y'.Modules)
    (hℱ : higherDirectImageAcyclic π ℱ) :
    higherDirectImageAcyclic π (Injective.under ℱ) ∧
      higherDirectImageAcyclic π (cokernel (Injective.ι ℱ)) := by
  let := HasDerivedCategory.standard Y'.Modules
  let := HasDerivedCategory.standard Y.Modules
  refine ⟨fun q ↦ (pushforward π).isZero_rightDerived_obj_injective_succ q _, fun q ↦ ?_⟩
  have hS : (ShortComplex.mk (Injective.ι ℱ) (cokernel.π (Injective.ι ℱ))
      (cokernel.condition _)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have h₂ := hS.rightDerivedδ_exact₂ (pushforward π) (q + 1)
  exact h₂.isZero_X₂ (((pushforward π).isZero_rightDerived_obj_injective_succ q _).eq_of_src _ _)
    ((hℱ (q + 1)).eq_of_tgt _ _)

variable (π) in
/-- **Cohomology of a pushforward with vanishing higher direct images.** For `π : Y' ⟶ Y`, the
functors `ℱ ↦ H^q(Y', ℱ)` and `ℱ ↦ H^q(Y, π_* ℱ)` are isomorphic on the `𝒪_{Y'}`-modules `ℱ`
with `R^p π_* ℱ = 0` for all `p > 0`. This is the degenerate case of the Leray spectral
sequence. -/
theorem nonempty_functorH_iso_pushforward_of_isZero_higherDirectImage (q : ℕ) :
    Nonempty ((higherDirectImageAcyclic π).ι ⋙ toAb Y' ⋙
        CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology Y') q ≅
      (higherDirectImageAcyclic π).ι ⋙ pushforward π ⋙ toAb Y ⋙
        CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology Y) q) := by
  have := enoughInjectives_of_hasInjectiveResolutions (C := Y'.Modules)
  have hf (S : ShortComplex Y'.Modules) (hS : S.ShortExact)
      (h : higherDirectImageAcyclic π S.X₁) : ((S.map (pushforward π)).map (toAb Y)).ShortExact :=
    shortExact_map_toSheaf (shortExact_map_pushforward_of_isZero hS (h 0))
  refine (higherDirectImageAcyclic π).nonempty_iso_of_connecting
    (higherDirectImageAcyclic_under_cokernel π)
    (fun q ↦ toAb Y' ⋙ CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology Y') q)
    (fun q ↦ pushforward π ⋙ toAb Y ⋙
      CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology Y) q)
    (fun S hS _ q ↦ CategoryTheory.Sheaf.functorHδ (shortExact_map_toSheaf hS) q)
    (fun S hS h q ↦ CategoryTheory.Sheaf.functorHδ (hf S hS h) q)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ q
  · intro S₁ S₂ φ h₁ h₂ _ _ q
    exact CategoryTheory.Sheaf.functorHδ_naturality.{u} (shortExact_map_toSheaf h₁) q
      (shortExact_map_toSheaf h₂) ((toAb Y').mapShortComplex.map φ)
  · intro S₁ S₂ φ h₁ h₂ p₁ p₂ q
    exact CategoryTheory.Sheaf.functorHδ_naturality.{u} (hf _ h₁ p₁) q (hf _ h₂ p₂)
      ((pushforward π ⋙ toAb Y).mapShortComplex.map φ)
  · intro S hS _ q x
    exact CategoryTheory.Sheaf.functorHδ_eq_zero_iff.{u} (shortExact_map_toSheaf hS) q x
  · intro S hS h q x
    exact CategoryTheory.Sheaf.functorHδ_eq_zero_iff.{u} (hf S hS h) q x
  · intro S hS _ q hinj
    have : Subsingleton (CategoryTheory.Sheaf.H (S.map (toAb Y')).X₂ (q + 1)) :=
      subsingleton_H_of_injective S.X₂ q
    exact CategoryTheory.Sheaf.functorHδ_surjective.{u} (shortExact_map_toSheaf hS) q
  · intro S hS h q hinj
    have : Subsingleton (CategoryTheory.Sheaf.H ((S.map (pushforward π)).map (toAb Y)).X₂
        (q + 1)) :=
      subsingleton_H_pushforward_of_injective π S.X₂ q
    exact CategoryTheory.Sheaf.functorHδ_surjective.{u} (hf S hS h) q
  · exact Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft (toAb Y')
          (CategoryTheory.Sheaf.functorHZeroIso.{u} _ isTerminalTop) ≪≫
        NatIso.ofComponents (fun _ ↦ Iso.refl _) ≪≫
        Functor.isoWhiskerLeft (pushforward π ⋙ toAb Y)
          (CategoryTheory.Sheaf.functorHZeroIso.{u} _ isTerminalTop).symm)

/-- **Cohomology of a pushforward with vanishing higher direct images, with its module
structure.** For `π : Y' ⟶ Y` and an `𝒪_{Y'}`-module `ℱ` with `R^p π_* ℱ = 0` for all `p > 0`,
`H^q(Y', ℱ) ≅ H^q(Y, π_* ℱ)`, the isomorphism taking the action of `π^♯ r` to that of `r`, for
every global function `r` on `Y`. -/
theorem exists_H_addEquiv_pushforward_of_isZero_higherDirectImage (ℱ : Y'.Modules)
    (hℱ : ∀ p : ℕ, IsZero ((higherDirectImage π (p + 1)).obj ℱ)) (q : ℕ) :
    ∃ e : ℱ.H q ≃+ ((pushforward π).obj ℱ).H q,
      ∀ (r : Γ(Y, ⊤)) (x : ℱ.H q), e (π.appTop r • x) = r • e x := by
  obtain ⟨e⟩ := nonempty_functorH_iso_pushforward_of_isZero_higherDirectImage π q
  let F : (higherDirectImageAcyclic π).FullSubcategory := ⟨ℱ, hℱ⟩
  refine ⟨(e.app F).addCommGroupIsoToAddEquiv, fun r x ↦ ?_⟩
  have h := NatTrans.naturality_apply e.hom
    (ObjectProperty.homMk (ℱ.smulHom (π.appTop r)) : F ⟶ F) x
  change e.hom.app F (H.map (ℱ.smulHom (π.appTop r)) q x) =
    H.map (((pushforward π).obj ℱ).smulHom r) q (e.hom.app F x)
  rw [← pushforward_map_smulHom]
  exact h

end AlgebraicGeometry.Scheme.Modules
