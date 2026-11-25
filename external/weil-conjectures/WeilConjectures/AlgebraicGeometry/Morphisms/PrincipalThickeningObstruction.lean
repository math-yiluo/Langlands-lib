/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import WeilConjectures.AlgebraicGeometry.Morphisms.PrincipalThickeningCokernelSections

/-! # The section obstruction sequence for principal thickenings

## References

* Stacks Project, Tags 01IH and 01QP (quotient structure sheaves), and Tag 01DZ, Section 20.2
  (cohomology as a universal delta-functor)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Multiplication by the defining power of a principal thickening on its ambient open. -/
noncomputable def principalThickeningMultiplication
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens) (n : ℕ) :
    SheafOfModules.unit W.toScheme.ringCatSheaf ⟶
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
  Modules.smulHom _ ((((ΓSpecIso (.of R)).inv ≫ W.ι.appTop) g) ^ (n + 1))

/-- The actual image ideal sheaf, rather than a chosen model of the defining ideal. -/
noncomputable abbrev principalThickeningIdeal
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens) (n : ℕ) :
    W.toScheme.Modules := image (principalThickeningMultiplication R g W n)

set_option backward.isDefEq.respectTransparency false in
private theorem boundary_naturality {X : Scheme.{u}} {S T : ShortComplex X.Modules}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) (x : S.X₃.H n) :
    Modules.H.δ hT n (Modules.H.map φ.τ₃ n x) =
      Modules.H.map φ.τ₁ (n + 1) (Modules.H.δ hS n x) := by
  let F := Modules.toAb X
  have hS' : (S.map F).ShortExact := Modules.shortExact_map_toSheaf hS
  have hT' : (T.map F).ShortExact := Modules.shortExact_map_toSheaf hT
  let φ' : S.map F ⟶ T.map F := F.mapShortComplex.map φ
  have he := ShortComplex.ShortExact.extClass_naturality
    (C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hS' hT' φ'
  change Abelian.Ext.comp (Abelian.Ext.comp x (Abelian.Ext.mk₀ (F.map φ.τ₃))
      (add_zero n)) hT'.extClass rfl =
    Abelian.Ext.comp (Abelian.Ext.comp x hS'.extClass rfl)
      (Abelian.Ext.mk₀ (F.map φ.τ₁)) (add_zero (n + 1))
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero,
    Abelian.Ext.comp_assoc_of_third_deg_zero]
  exact congrArg (fun z ↦ Abelian.Ext.comp x z rfl) he.symm

set_option backward.isDefEq.respectTransparency false in
/-- Exactness and naturality of the section obstruction sequence. -/
theorem principal_thickening_obstruction
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens) :
    ∃ δ : ∀ n : ℕ, Γ(FiniteEtale.Adic.openThickening
        (Ideal.Quotient.mk (Ideal.span {g})) W n, ⊤) →+
          Modules.H (principalThickeningIdeal R g W n) 1,
      (∀ n t, δ n t = 0 → ∃ a : Γ(W.toScheme, ⊤),
        (FiniteEtale.Adic.openThickeningMap
          (Ideal.Quotient.mk (Ideal.span {g})) W n).appTop a = t) ∧
      (∀ (n m : ℕ)
        (κ : principalThickeningIdeal R g W m ⟶ principalThickeningIdeal R g W n)
        (h : FiniteEtale.Adic.openThickening
            (Ideal.Quotient.mk (Ideal.span {g})) W n ⟶
          FiniteEtale.Adic.openThickening (Ideal.Quotient.mk (Ideal.span {g})) W m),
        κ ≫ image.ι (principalThickeningMultiplication R g W n) =
            image.ι (principalThickeningMultiplication R g W m) →
        h ≫ FiniteEtale.Adic.openThickeningMap
            (Ideal.Quotient.mk (Ideal.span {g})) W m =
          FiniteEtale.Adic.openThickeningMap
            (Ideal.Quotient.mk (Ideal.span {g})) W n →
        ∀ t, δ n (h.appTop t) = Modules.H.map κ 1 (δ m t)) := by
  classical
  let p := fun n : ℕ ↦ Modules.smulHom (SheafOfModules.unit W.toScheme.ringCatSheaf)
    ((((ΓSpecIso (.of R)).inv ≫ W.ι.appTop) g) ^ (n + 1))
  let i := fun n : ℕ ↦ image.ι (p n)
  let S := fun n : ℕ ↦ ShortComplex.mk (i n) (cokernel.π (i n)) (cokernel.condition _)
  have hS (n : ℕ) : (S n).ShortExact := { exact := ShortComplex.exact_cokernel (i n) }
  obtain ⟨e, he, hn⟩ := principal_thickening_cokernel_sections R g W
  let δ := fun n : ℕ ↦ (Modules.H.δ (hS n) 0).comp (e n).symm.toAddMonoidHom
  refine ⟨δ, ?_, ?_⟩
  · intro n t ht
    have hz : (e n).symm t ∈ (Modules.H.δ (hS n) 0).ker := ht
    rw [Modules.H.ker_δ_eq_range_map_g (hS n) 0] at hz
    obtain ⟨a, ha⟩ := hz
    refine ⟨Modules.H.zeroLinearEquiv (S n).X₂ a, ?_⟩
    rw [← he]
    change (e n) (Modules.H.map (S n).g 0
      ((Modules.H.zeroLinearEquiv (S n).X₂).symm
        (Modules.H.zeroLinearEquiv (S n).X₂ a))) = t
    rw [LinearEquiv.symm_apply_apply]
    exact (congrArg (e n) ha).trans ((e n).apply_symm_apply t)
  · intro n m κ h hk hh t
    change κ ≫ i n = i m at hk
    let q := cokernel.map (i m) (i n) κ (𝟙 _) (by simpa using hk.symm)
    let φ : S m ⟶ S n :=
      { τ₁ := κ
        τ₂ := 𝟙 _
        τ₃ := q
        comm₁₂ := by simpa [S] using hk
        comm₂₃ := by simp [S, q] }
    have hq : (e n).symm (h.appTop t) = Modules.H.map q 0 ((e m).symm t) := by
      apply (e n).injective
      rw [(e n).apply_symm_apply]
      simpa only [AddEquiv.apply_symm_apply] using (hn n m κ h hk hh ((e m).symm t)).symm
    change Modules.H.δ (hS n) 0 ((e n).symm (h.appTop t)) =
      Modules.H.map κ 1 (Modules.H.δ (hS m) 0 ((e m).symm t))
    rw [hq]
    exact boundary_naturality (hS m) (hS n) φ 0 ((e m).symm t)

end AlgebraicGeometry.Scheme
