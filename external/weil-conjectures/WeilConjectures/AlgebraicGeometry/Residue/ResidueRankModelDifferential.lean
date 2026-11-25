/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
import WeilConjectures.AlgebraicGeometry.Affine.AffineFreeResidueSectionsCohomology
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Residue vanishing of the differential in a Betti-rank model

## References

* Stacks Project, Tag 0BCD, minimal free model
* Tag 0BF2, first source complex
* Stacks Project, Tag 0BCD and Tag 0BF2, first displayed source complex
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem finite_rank_scalarExtension
    {A κ : Type v} [CommRing A] [Field κ] (ρ : A →+* κ)
    (M : ModuleCat.{v} A) (n : ℕ) (e : M ≃ₗ[A] (ULift.{v} (Fin n) → A)) :
    Module.Finite κ ((ModuleCat.extendScalars ρ).obj M) ∧
      Module.finrank κ ((ModuleCat.extendScalars ρ).obj M) = n := by
  have : Module.Free A M := Module.Free.of_equiv e.symm
  have : Module.Finite A M := Module.Finite.equiv e.symm
  let := ρ.toAlgebra
  have : Nontrivial A := ρ.domain_nontrivial
  constructor
  · change Module.Finite κ (TensorProduct A κ M)
    infer_instance
  · change Module.finrank κ (TensorProduct A κ M) = n
    rw [Module.finrank_baseChange, e.finrank_eq]
    simp

private theorem differential_zero_of_equal_dimensions
    {κ : Type v} [Field κ] (C : CochainComplex (ModuleCat.{v} κ) ℤ)
    (hfinite : ∀ j : ℤ, Module.Finite κ (C.X j))
    (hhomfinite : ∀ j : ℤ, Module.Finite κ (C.homology j))
    (hdim : ∀ j : ℤ, Module.finrank κ (C.homology j) = Module.finrank κ (C.X j)) :
    ∀ i j : ℤ, C.d i j = 0 := by
  intro i j
  have : Module.Finite κ (C.X i) := hfinite i
  have hi := (ModuleCat.mono_iff_injective (C.iCycles i)).mp inferInstance
  have hp := (ModuleCat.epi_iff_surjective (C.homologyπ i)).mp inferInstance
  have : Module.Finite κ (C.cycles i) := Module.Finite.of_injective (C.iCycles i).hom hi
  have : Module.Finite κ (C.homology i) :=
    hhomfinite i
  have hrank : Module.finrank κ (C.cycles i) = Module.finrank κ (C.X i) :=
    Nat.le_antisymm (LinearMap.finrank_le_finrank_of_injective hi) (by
      rw [← hdim i]
      exact LinearMap.finrank_le_finrank_of_surjective hp)
  have hsurj : Function.Surjective (C.iCycles i).hom :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hi
  have : Epi (C.iCycles i) := (ModuleCat.epi_iff_surjective _).mpr hsurj
  apply (cancel_epi (C.iCycles i)).mp
  rw [CategoryTheory.Limits.comp_zero]
  exact C.iCycles_d i j

/-- Every degree-zero differential coordinate of a bounded Betti-rank model has zero residue. -/
theorem residueRankModel_differential_eval_eq_zero
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (w : W)
    (hfin : ∀ j : ℤ, Module.Finite (W.residueField w) (derivedFiberCohomology W E j w))
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (K : CochainComplex (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j))
    (hrank : ∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := (moduleRings W.toRingedSpace).over U)
      (ULift.{v} (Fin (derivedFiberBetti W E j w)))))
    (he : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K))
    (m : ℕ)
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (t : (K.X 0).val.obj (.op (Over.mk (𝟙 U)))) :
    ∀ i, W.evaluation U w hwU
      (e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) t) i) = 0 := by
  let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) := SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
  have : F.Additive := inferInstanceAs
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
  let ρ := (W.evaluation U w hwU).hom
  let T := ModuleCat.extendScalars.{v, v, v} ρ
  have : T.Additive := (ModuleCat.extendRestrictScalarsAdj ρ).left_adjoint_additive
  let C := ((F ⋙ T).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have hC := affineFree_residueSections_cohomologyLinearEquiv W E w U hwU hU K hb
    (fun j ↦ derivedFiberBetti W E j w) hrank he
  have hterms (j : ℤ) : Module.Finite (W.residueField w) (C.X j) ∧
      Module.finrank (W.residueField w) (C.X j) = derivedFiberBetti W E j w := by
    classical
    exact finite_rank_scalarExtension ρ (F.obj (K.X j)) (derivedFiberBetti W E j w)
      (SheafOfModules.sectionsLinearEquivOfIsoFree (hrank j).some
        (.op (Over.mk (𝟙 U))))
  have hhomfinite (j : ℤ) : Module.Finite (W.residueField w) (C.homology j) := by
    have := hfin j
    exact Module.Finite.equiv (hC j).some
  have hdim (j : ℤ) : Module.finrank (W.residueField w) (C.homology j) =
      derivedFiberBetti W E j w := (hC j).some.finrank_eq.symm
  have hzero : C.d 0 1 = 0 := differential_zero_of_equal_dimensions C
    (fun j ↦ (hterms j).1) hhomfinite
    (fun j ↦ (hdim j).trans (hterms j).2.symm) 0 1
  intro i
  let q : F.obj (K.X 1) ⟶ (ModuleCat.restrictScalars ρ).obj
      (ModuleCat.of (W.residueField w) (W.residueField w)) :=
    ModuleCat.ofHom (X := F.obj (K.X 1))
      (Y := (ModuleCat.restrictScalars ρ).obj
        (ModuleCat.of (W.residueField w) (W.residueField w)))
      { toFun := fun x ↦ ρ (e1 x i)
        map_add' := by intro x y; simp
        map_smul' := by
          intro r x
          change ρ (e1 (r • x) i) = ρ r * ρ (e1 x i)
          simp [map_smul, Pi.smul_apply, smul_eq_mul] }
  let a := (ModuleCat.extendRestrictScalarsAdj ρ).homEquiv _ _ |>.symm q
  have ha := ((ModuleCat.extendRestrictScalarsAdj ρ).homEquiv _ _).apply_symm_apply q
  have hz : T.map (F.map (K.d 0 1)) ≫ a = 0 := by
    change C.d 0 1 ≫ a = 0
    rw [hzero, zero_comp]
  have hq : F.map (K.d 0 1) ≫ q = 0 := by
    rw [← ha, ← (ModuleCat.extendRestrictScalarsAdj ρ).homEquiv_naturality_left]
    rw [hz]
    exact (ModuleCat.extendRestrictScalarsAdj ρ).homAddEquiv_zero _ _
  exact ConcreteCategory.congr_hom hq t

end AlgebraicGeometry.Scheme
