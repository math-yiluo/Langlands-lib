/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Finitely presented modules and filtered colimits

Let `F : J ⥤ ModuleCat R` be a filtered diagram whose colimit is computed on underlying types,
with colimit cocone `c`. A linear map from a finitely presented module `M` to the colimit
`c.pt` factors through some `F.obj j`
(`ModuleCat.exists_lift_of_isColimit_of_finitePresentation`): the images of finitely many
generators lift to a common stage, and the finitely many relations, which hold in the colimit,
already hold at a later stage.
-/

@[expose] public section

universe w r v u

open CategoryTheory Limits

namespace ModuleCat

variable {R : Type u} [Ring R] {J : Type w} [Category.{r} J] [IsFiltered J]
  {F : J ⥤ ModuleCat.{v} R} [PreservesColimit F (forget (ModuleCat.{v} R))]
  {c : Cocone F} (hc : IsColimit c)

include hc in
/-- Finitely many elements of a stage of a filtered colimit of modules which vanish in the
colimit vanish at a common later stage. -/
lemma exists_map_eq_zero_of_isColimit {j : J} (S : Finset (F.obj j))
    (hS : ∀ x ∈ S, c.ι.app j x = 0) :
    ∃ (k : J) (h : j ⟶ k), ∀ x ∈ S, F.map h x = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨j, 𝟙 j, by simp⟩
  | insert x S _ ih =>
    obtain ⟨k, h, hk⟩ := ih fun y hy ↦ hS y (Finset.mem_insert_of_mem hy)
    have hx : c.ι.app k (F.map h x) = c.ι.app k 0 := by
      rw [map_zero, ← ConcreteCategory.comp_apply, c.w]
      exact hS x (Finset.mem_insert_self _ _)
    obtain ⟨l, f₁, f₂, e⟩ := Concrete.isColimit_exists_of_rep_eq F hc _ _ hx
    refine ⟨l, h ≫ f₁, fun y hy ↦ ?_⟩
    rw [F.map_comp, ConcreteCategory.comp_apply]
    rcases Finset.mem_insert.1 hy with rfl | hy
    · rw [e, map_zero]
    · rw [hk y hy, map_zero]

include hc in
/-- A linear map from a finite free module to a filtered colimit of modules factors through
some stage. -/
lemma exists_lift_pi_of_isColimit {n : ℕ} (φ : (Fin n → R) →ₗ[R] c.pt) :
    ∃ (j : J) (β : (Fin n → R) →ₗ[R] F.obj j), (c.ι.app j).hom ∘ₗ β = φ := by
  classical
  choose j y hy using fun i : Fin n ↦ Concrete.isColimit_exists_rep F hc (φ (Pi.single i 1))
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  have g (i : Fin n) : j i ⟶ k := (hk (Finset.mem_image_of_mem j (Finset.mem_univ i))).some
  refine ⟨k, ∑ i, (LinearMap.proj i).smulRight (F.map (g i) (y i)), ?_⟩
  refine LinearMap.pi_ext fun i a ↦ ?_
  have hi : c.ι.app k (F.map (g i) (y i)) = φ (Pi.single i 1) := by
    rw [← ConcreteCategory.comp_apply, c.w]
    exact hy i
  have e : Pi.single i a = a • (Pi.single i 1 : Fin n → R) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  have hβ : (∑ i, (LinearMap.proj i).smulRight (F.map (g i) (y i)) :
      (Fin n → R) →ₗ[R] F.obj k) (Pi.single i a) = a • F.map (g i) (y i) := by
    rw [LinearMap.sum_apply, Finset.sum_eq_single i
      (fun b _ hb ↦ by rw [LinearMap.smulRight_apply, LinearMap.proj_apply,
        Pi.single_eq_of_ne hb, zero_smul]) (by simp),
      LinearMap.smulRight_apply, LinearMap.proj_apply, Pi.single_eq_same]
  rw [LinearMap.comp_apply, hβ, map_smul, e, map_smul]
  exact congrArg (a • ·) hi

include hc in
/-- **Finitely presented modules are compact for filtered colimits.** A linear map from a
finitely presented module to a filtered colimit of modules factors through some stage. -/
theorem exists_lift_of_isColimit_of_finitePresentation (M : Type*) [AddCommGroup M]
    [Module R M] [Module.FinitePresentation R M] (φ : M →ₗ[R] c.pt) :
    ∃ (j : J) (α : M →ₗ[R] F.obj j), (c.ι.app j).hom ∘ₗ α = φ := by
  classical
  obtain ⟨n, m, f, g, hf, hfg⟩ := Module.FinitePresentation.exists_fin' R M
  obtain ⟨j, β, hβ⟩ := exists_lift_pi_of_isColimit hc (φ ∘ₗ f)
  obtain ⟨k, h, hk⟩ := exists_map_eq_zero_of_isColimit hc
    (Finset.univ.image fun i : Fin m ↦ β (g (Pi.single i 1))) (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      have := LinearMap.congr_fun hβ (g (Pi.single i 1))
      simp only [LinearMap.coe_comp, Function.comp_apply] at this
      erw [this]
      exact (congrArg φ (hfg.apply_apply_eq_zero _)).trans (map_zero φ))
  let β' : (Fin n → R) →ₗ[R] F.obj k := (F.map h).hom ∘ₗ β
  have hβ'g : β' ∘ₗ g = 0 := by
    refine LinearMap.pi_ext fun i a ↦ ?_
    have e : Pi.single i a = a • (Pi.single i 1 : Fin m → R) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply, β']
    rw [e, map_smul, map_smul, map_smul]
    erw [hk _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))]
    rw [smul_zero]
  have hker : LinearMap.ker f ≤ LinearMap.ker β' := by
    intro x hx
    obtain ⟨y, rfl⟩ := (hfg x).1 hx
    exact LinearMap.congr_fun hβ'g y
  refine ⟨k, (LinearMap.ker f).liftQ β' hker ∘ₗ (f.quotKerEquivOfSurjective hf).symm.toLinearMap,
    ?_⟩
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := hf x
  have := LinearMap.congr_fun hβ y
  simp only [LinearMap.coe_comp, Function.comp_apply] at this
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply, β']
  exact (ConcreteCategory.congr_hom (c.w h) (β y)).trans this

end ModuleCat
