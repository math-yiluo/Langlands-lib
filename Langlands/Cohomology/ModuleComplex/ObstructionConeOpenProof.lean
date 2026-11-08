import Langlands.Cohomology.ModuleComplex.ObstructionConeOpenStatement
import Langlands.Cohomology.ModuleComplex.BoundedFlatComplexProjectiveProof
import Langlands.Cohomology.ModuleComplex.ObstructionCone.ExactSpread
import Langlands.Cohomology.ModuleComplex.ObstructionCone.QuasiIsoModule
import Langlands.Cohomology.ModuleComplex.ObstructionCone.Transfer
import Langlands.Cohomology.ModuleComplex.ObstructionCone.Model

/-! # Openness of first-cohomology vanishing for an obstruction cone: proof -/

set_option autoImplicit false

universe u

open TensorProduct

noncomputable section

namespace Langlands.Cohomology.ModuleComplex.ObstructionCone

/-- Middle exactness after `⊗ k` on the right is middle exactness after base change. -/
lemma exact_baseChange_of_exact_rTensor {A : Type u} [CommRing A] {F₁ F₂ F₃ : Type u}
    [AddCommGroup F₁] [Module A F₁] [AddCommGroup F₂] [Module A F₂] [AddCommGroup F₃]
    [Module A F₃] (a : F₁ →ₗ[A] F₂) (b : F₂ →ₗ[A] F₃) (k : Type u) [CommRing k] [Algebra A k]
    (h : Function.Exact (a.rTensor k) (b.rTensor k)) :
    Function.Exact (a.baseChange k) (b.baseChange k) := by
  have h₁ : (a.baseChange k).restrictScalars A ∘ₗ (TensorProduct.comm A F₁ k).toLinearMap =
      (TensorProduct.comm A F₂ k).toLinearMap ∘ₗ a.rTensor k := by
    apply TensorProduct.ext'
    intro x c
    simp
  have h₂ : (b.baseChange k).restrictScalars A ∘ₗ (TensorProduct.comm A F₂ k).toLinearMap =
      (TensorProduct.comm A F₃ k).toLinearMap ∘ₗ b.rTensor k := by
    apply TensorProduct.ext'
    intro x c
    simp
  exact (Function.Exact.iff_of_ladder_linearEquiv h₁ h₂).mpr h

/-- A scalar that is a unit in an algebra acts bijectively on every module over it. -/
lemma smul_bijective_of_isUnit {A S M : Type u} [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module S M] [Module A M] [IsScalarTower A S M] {g : A}
    (hg : IsUnit (algebraMap A S g)) : Function.Bijective (fun m : M => g • m) := by
  obtain ⟨v, hv⟩ := hg
  have h : (fun m : M => g • m) = fun m => (v : S) • m := by
    funext m
    rw [hv, algebraMap_smul]
  rw [h]
  refine ⟨fun m m' hm => ?_, fun m => ⟨(↑v⁻¹ : S) • m, by simp [smul_smul]⟩⟩
  have := congrArg (fun x : M => (↑v⁻¹ : S) • x) hm
  simpa [smul_smul] using this

/-- Openness of first-cohomology vanishing for an obstruction cone over a noetherian ring. -/
theorem openStatement : OpenStatement.{u} := by
  intro A _ _ C _ _ _ d hdd n hbdd hfin0 hfin F Q _ _ _ _ _ _ _ δ θ z hθ hz k _ _ hk
  obtain ⟨K, _, _, _, _, dK, hdKK, hKbdd, φ, hφ, h0inj, h0surj, hinj, hsurj⟩ :=
    boundedFlatComplexProjective A C d hdd n hbdd hfin0 hfin
  have hCoh : ∀ (N : Type u) [AddCommGroup N] [Module A N], Transfer.CohIso K C dK d φ N :=
    fun N _ _ => QuasiIsoModule.rTensor_quasiIso K dK hdKK C d hdd n hKbdd hbdd φ hφ h0inj
      h0surj hinj hsurj N
  obtain ⟨zh, w, θh, v, hzh, hφzh, hθh, hφθh⟩ :=
    Transfer.exists_transfer hφ (hCoh Q) (hCoh F) δ θ z hθ hz
  have hKk := Transfer.hOneVanishes_model hφ δ θ z zh w θh v hφzh hθh hφθh k (hCoh k) hk
  -- a finite free presentation of `Q`
  obtain ⟨n₀, p, hp⟩ := Module.Finite.exists_fin' A Q
  obtain ⟨n₁, g', hg'⟩ := Module.Finite.exists_fin' A (LinearMap.ker p)
  let g : (Fin n₁ → A) →ₗ[A] (Fin n₀ → A) := (LinearMap.ker p).subtype ∘ₗ g'
  have hgp : Function.Exact g p := by
    rw [LinearMap.exact_iff, LinearMap.range_comp, LinearMap.range_eq_top.mpr hg',
      Submodule.map_top, Submodule.range_subtype]
  have hpg : p ∘ₗ g = 0 := hgp.linearMap_comp_eq_zero
  obtain ⟨z₀, hz₀⟩ := LinearMap.lTensor_surjective (K 2) hp zh
  have hdK : dK 1 ∘ₗ dK 0 = 0 := hdKK 0
  have hba := Model.b_comp_a dK δ p g θh z₀ hpg zh hz₀ hθh hdK
  have hexk : Function.Exact ((Model.a dK δ p θh).baseChange k) ((Model.b dK g z₀).baseChange k) :=
    exact_baseChange_of_exact_rTensor _ _ k ((Model.exact_rTensor_iff dK δ p g θh z₀ k).mpr
      ((Model.exact_aM_bM_iff dK δ p g θh z₀ k hp hgp zh hz₀ hθh hdK).mpr hKk))
  obtain ⟨g₀, hg₀, hspread⟩ := ExactSpread.exists_exact_rTensor_spread _ _ hba k hexk
  refine ⟨g₀, hg₀, fun S _ _ hS M _ _ _ _ => ?_⟩
  have hM := hspread M (smul_bijective_of_isUnit (S := S) hS)
  have hKM := (Model.exact_aM_bM_iff dK δ p g θh z₀ M hp hgp zh hz₀ hθh hdK).mp
    ((Model.exact_rTensor_iff dK δ p g θh z₀ M).mp hM)
  exact Transfer.hOneVanishes_of_model hφ δ θ z zh w θh v hzh hφzh hφθh M (hCoh M) hKM

end Langlands.Cohomology.ModuleComplex.ObstructionCone
