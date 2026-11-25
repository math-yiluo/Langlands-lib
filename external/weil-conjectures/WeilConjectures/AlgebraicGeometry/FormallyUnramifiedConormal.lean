/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickeningExists
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.KernelTensorPullbackIsoExists

/-!
# Conormal sheaf of a formally unramified morphism

Source: Stacks Project, More on Morphisms, Definition 04F4 (2), and Morphisms,
Definition 01R2 (blueprint: def-weil-pbc-conormal-sheaf-formally-unramified).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- The conormal sheaf for the chosen universal first order thickening of `h`.
Its ideal is `i.ker`, and its square is zero by `H.1.2`; hence pulling back the ideal
is the same conormal module as pulling back its quotient by its square.
Source: Stacks Project, Definition 04F4 (2) and Definition 01R2
(blueprint: def-weil-pbc-conormal-sheaf-formally-unramified). -/
noncomputable def formallyUnramifiedConormal {Z X Z' : Scheme.{u}}
    (h : Z ⟶ X) [FormallyUnramified h] (i : Z ⟶ Z') (h' : Z' ⟶ X)
    (_H : IsUniversalFirstOrderThickening h i h') : Z.Modules :=
  (Scheme.Modules.tensorPullback i).obj i.ker.toModules

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem range_kernelIdeal {A B : Scheme.{u}} (i : A ⟶ B)
    [IsClosedImmersion i] (U : B.Opens) :
    Set.range (i.ker.toModulesι.app U) = {x | i.app U x = 0} := by
  rw [Scheme.IdealSheafData.range_toModulesι_app_eq]
  ext x
  change i.imageι.app U x = 0 ↔ i.app U x = 0
  have hi := Scheme.Hom.congr_app i.toImage_imageι U
  rw [Scheme.Hom.comp_app] at hi
  have hcomp : (i.imageι.app U ≫ i.toImage.app (i.imageι ⁻¹ᵁ U)) x = 0 ↔
      i.app U x = 0 := by
    rw [hi]
    have heq {V W : A.Opens} (he : V = W) (y : Γ(A, W)) :
        A.presheaf.map (eqToHom he).op y = 0 ↔ y = 0 :=
      map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
        (A.presheaf.map (eqToHom he).op)).1
    exact heq _ _
  exact (map_eq_zero_iff _
    (ConcreteCategory.bijective_of_isIso (i.toImage.app (i.imageι ⁻¹ᵁ U))).1).symm.trans
      hcomp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem kernelIdeal_section_lift {Z Z₁ Z₂ : Scheme.{u}}
    (i₁ : Z ⟶ Z₁) (i₂ : Z ⟶ Z₂) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (φ : Z₁ ⟶ Z₂) (hc : i₁ ≫ φ = i₂) (U : Z₂.Opens)
    (s₂ : Γ(i₂.ker.toModules, U)) :
    ∃ s₁ : Γ(i₁.ker.toModules, φ ⁻¹ᵁ U),
      i₁.ker.toModulesι.app (φ ⁻¹ᵁ U) s₁ = φ.app U (i₂.ker.toModulesι.app U s₂) := by
  have hz : i₂.app U (i₂.ker.toModulesι.app U s₂) = 0 := by
    have hm : i₂.ker.toModulesι.app U s₂ ∈ Set.range (i₂.ker.toModulesι.app U) :=
      ⟨s₂, rfl⟩
    rwa [range_kernelIdeal] at hm
  have hc' := Scheme.Hom.congr_app hc U
  rw [Scheme.Hom.comp_app] at hc'
  have hz₁ : i₁.app (φ ⁻¹ᵁ U) (φ.app U (i₂.ker.toModulesι.app U s₂)) = 0 := by
    have hh := congrArg (fun f ↦ f (i₂.ker.toModulesι.app U s₂)) hc'
    simpa only [CommRingCat.comp_apply, hz, map_zero, Scheme.Hom.comp_base,
      Opens.map_comp_obj] using hh
  have hm : φ.app U (i₂.ker.toModulesι.app U s₂) ∈
      Set.range (i₁.ker.toModulesι.app (φ ⁻¹ᵁ U)) := by
    rw [range_kernelIdeal]
    exact hz₁
  exact hm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorPullback_hom_ext {A B : Scheme.{u}} (g : A ⟶ B)
    (adj : Scheme.Modules.tensorPullback g ⊣ Scheme.Modules.pushforward g)
    (M : B.Modules) (N : A.Modules)
    (f₁ f₂ : (Scheme.Modules.tensorPullback g).obj M ⟶ N)
    (H : ∀ (U : B.Opens) (s : Γ(M, U)),
      f₁.app (g ⁻¹ᵁ U)
        ((adj.unit.app M).app
          U s) =
      f₂.app (g ⁻¹ᵁ U)
        ((adj.unit.app M).app
          U s)) : f₁ = f₂ := by
  apply (adj.homEquiv M N).injective
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  change (adj.homEquiv M N f₁).app U s = (adj.homEquiv M N f₂).app U s
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforward_map_app]
  exact H U s

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Existence of a choice and independence of the conormal sheaf under the unique
compatible comparison of universal thickenings. The module isomorphism is uniquely
determined by carrying the pullback of each ideal section to the pullback of its
image under the scheme comparison. The restrictions to `W` put both sections on
the same open of `Z`.
Source: Stacks Project, Tags 04F2, 04F3, 04F4 (2) and 01R2
(blueprint: def-weil-pbc-conormal-sheaf-formally-unramified).
Proof: (1) Use `FormallyUnramified.exists_universalFirstOrderThickening` to obtain
one universal thickening and the unique compatible isomorphism between any two.
(2) Its ideal is the kernel ideal sheaf (def-sbc-closed-immersion-ideal-sheaf);
first order means its square is zero, so the quotient by the square is the ideal.
(3) Apply the tensor module pullback (def-pc-module-pullback) to that ideal.
(4) The compatible scheme isomorphism identifies the two kernel ideal sheaves;
functoriality of tensor pullback identifies their pullbacks on the common `Z`.
The scheme comparison is unique by the universal property, so this identification
is canonical and independent of the chosen thickening. Pullbacks of ideal sections
locally generate the conormal module, so the displayed section equation determines
the module isomorphism uniquely. -/
theorem formallyUnramifiedConormal_independent {Z X : Scheme.{u}}
    (h : Z ⟶ X) [FormallyUnramified h] :
    (∃ (Z' : Scheme.{u}) (i : Z ⟶ Z') (h' : Z' ⟶ X),
      IsUniversalFirstOrderThickening h i h') ∧
    ∀ (Z₁ Z₂ : Scheme.{u}) (i₁ : Z ⟶ Z₁) (h₁ : Z₁ ⟶ X)
      (i₂ : Z ⟶ Z₂) (h₂ : Z₂ ⟶ X)
      (H₁ : IsUniversalFirstOrderThickening h i₁ h₁)
      (H₂ : IsUniversalFirstOrderThickening h i₂ h₂),
      ((∃! φ : Z₁ ⟶ Z₂, φ ≫ h₂ = h₁ ∧ i₁ ≫ φ = i₂) ∧
        ∀ φ : Z₁ ⟶ Z₂, φ ≫ h₂ = h₁ → i₁ ≫ φ = i₂ → IsIso φ) ∧
      ∀ (φ : Z₁ ⟶ Z₂), φ ≫ h₂ = h₁ → i₁ ≫ φ = i₂ →
        ∃! e : formallyUnramifiedConormal h i₂ h₂ H₂ ≅
            formallyUnramifiedConormal h i₁ h₁ H₁,
          ∀ (U : Z₂.Opens) (s₂ : Γ(i₂.ker.toModules, U))
            (s₁ : Γ(i₁.ker.toModules, φ ⁻¹ᵁ U)),
            i₁.ker.toModulesι.app (φ ⁻¹ᵁ U) s₁ =
              φ.app U (i₂.ker.toModulesι.app U s₂) →
            ∀ (W : Z.Opens) (a : W ≤ i₂ ⁻¹ᵁ U) (b : W ≤ i₁ ⁻¹ᵁ (φ ⁻¹ᵁ U)),
              e.hom.app W
                  ((formallyUnramifiedConormal h i₂ h₂ H₂).val.map (homOfLE a).op
                    (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
                      i₂)).unit.app i₂.ker.toModules).app U s₂)) =
                (formallyUnramifiedConormal h i₁ h₁ H₁).val.map (homOfLE b).op
                  (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
                    i₁)).unit.app i₁.ker.toModules).app (φ ⁻¹ᵁ U) s₁) := by
  obtain ⟨hex, hcompare⟩ := FormallyUnramified.exists_universalFirstOrderThickening h
  refine ⟨hex, ?_⟩
  intro Z₁ Z₂ i₁ h₁ i₂ h₂ H₁ H₂
  have hunique := hcompare Z₁ Z₂ i₁ h₁ i₂ h₂ H₁ H₂
  refine ⟨hunique, ?_⟩
  intro φ hφ hi
  have : IsIso φ := hunique.2 φ hφ hi
  have : IsClosedImmersion i₁ := H₁.1.1
  have : IsClosedImmersion i₂ := H₂.1.1
  obtain ⟨e, he⟩ := exists_kernelTensorPullbackIso i₁ i₂ φ hi
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply tensorPullback_hom_ext i₂
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i₂))
  intro U s₂
  obtain ⟨s₁, hs₁⟩ := kernelIdeal_section_lift i₁ i₂ φ hi U s₂
  have hb : i₂ ⁻¹ᵁ U ≤ i₁ ⁻¹ᵁ (φ ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, hi]
  have h₁ := he' U s₂ s₁ hs₁ (i₂ ⁻¹ᵁ U) le_rfl hb
  have h₂ := he U s₂ s₁ hs₁ (i₂ ⁻¹ᵁ U) le_rfl hb
  simp only [homOfLE_refl, op_id, PresheafOfModules.map_id] at h₁ h₂
  exact h₁.trans h₂.symm

end AlgebraicGeometry
