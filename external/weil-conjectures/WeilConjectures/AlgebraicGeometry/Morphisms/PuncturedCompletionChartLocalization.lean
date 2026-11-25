/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionChartSectionModules
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-! # Localization of affine chart sections

## References

* Stacks Project, Tag 0BLH, first two proof paragraphs
* Stacks Project, Tag 05EL, item (1)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- Localization of one affine chart identifies its sections with overlap sections. -/
theorem exists_chart_section_localization
    {A : Type u} [CommRing A] {Y : Scheme.{u}} (h : Y ⟶ Spec (.of A))
    (a g : A) (hV : IsAffineOpen (h ⁻¹ᵁ PrimeSpectrum.basicOpen g))
    (U : Y.Opens) (hU : U = (h ⁻¹ᵁ PrimeSpectrum.basicOpen a) ⊓
      (h ⁻¹ᵁ PrimeSpectrum.basicOpen g)) :
    letI : Module A Γ(Y, U) := Module.compHom _
      ((ΓSpecIso (.of A)).inv ≫ h.appTop ≫
        Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
    ∃ e : FormalGlueing.localize a (FormalGlueing.piece g (chartSectionModule h g)) ≃ₗ[A]
        Γ(Y, U),
      ∀ m, e (LocalizedModule.mk m 1) =
        Y.presheaf.map (homOfLE (hU.le.trans inf_le_right)).op m := by
  classical
  dsimp
  let V := h ⁻¹ᵁ PrimeSpectrum.basicOpen g
  let φ : A →+* Γ(Y, V) := ((ΓSpecIso (.of A)).inv ≫ h.appTop ≫
    Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom
  let ρ : Γ(Y, V) →+* Γ(Y, U) :=
    (Y.presheaf.map (homOfLE (hU.le.trans inf_le_right)).op).hom
  let ψ : A →+* Γ(Y, U) := ((ΓSpecIso (.of A)).inv ≫ h.appTop ≫
    Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
  have hcomp : ρ.comp φ = ψ := by
    ext x
    change ( (ΓSpecIso (.of A)).inv ≫ h.appTop ≫
      Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫
      Y.presheaf.map (homOfLE (hU.le.trans inf_le_right)).op) x = _
    rw [← Y.presheaf.map_comp]
    rfl
  let : Algebra A Γ(Y, V) := φ.toAlgebra
  let : Algebra Γ(Y, V) Γ(Y, U) := ρ.toAlgebra
  let : Algebra A Γ(Y, U) := ψ.toAlgebra
  have : IsScalarTower A Γ(Y, V) Γ(Y, U) :=
    IsScalarTower.of_algebraMap_eq' hcomp.symm
  have hopen : U = Y.basicOpen (φ a) := by
    rw [hU]
    change _ = Y.basicOpen (Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
      (h.appTop ((ΓSpecIso (.of A)).inv a)))
    rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine,
      inf_comm]
  let : IsLocalization.Away (φ a) Γ(Y, U) :=
    hV.isLocalization_of_eq_basicOpen (φ a)
      (homOfLE (hU.le.trans inf_le_right)) hopen
  have : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, V) (Submonoid.powers a))
      Γ(Y, U) := by
    rw [Algebra.algebraMapSubmonoid_powers]
    exact inferInstanceAs (IsLocalization.Away (φ a) Γ(Y, U))
  let e₀ : FormalGlueing.piece g (chartSectionModule h g) ≃ₗ[A] Γ(Y, V) :=
    { toFun := fun m ↦ m
      invFun := fun m ↦ m
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a m ↦ chartSectionModule_smul h g a m }
  let d := (IsScalarTower.toAlgHom A Γ(Y, V) Γ(Y, U)).toLinearMap.comp e₀.toLinearMap
  have : IsLocalizedModule (Submonoid.powers a) d :=
    IsLocalizedModule.of_linearEquiv_right _ _ e₀
  refine ⟨IsLocalizedModule.linearEquiv (Submonoid.powers a)
    (LocalizedModule.mkLinearMap _ _) d, ?_⟩
  intro m
  exact IsLocalizedModule.linearEquiv_apply (Submonoid.powers a)
    (LocalizedModule.mkLinearMap _ _) d m


end AlgebraicGeometry.Scheme.CompletionGluingData
