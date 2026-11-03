import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Nonzero components under scalar extension of an internal direct sum -/

noncomputable section

open scoped TensorProduct

namespace Langlands.LinearAlgebra

variable {k K V W ι κ : Type*} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module K W]

open Classical in
/-- The coordinate projection associated to an internal direct sum of submodules. -/
def internalComponentProjection (B : κ → Submodule K W)
    (hB : DirectSum.IsInternal B) (j : κ) : W →ₗ[K] B j :=
  (DirectSum.component K κ (fun j => B j) j).comp
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap B) hB).symm.toLinearMap

open Classical in
/-- If pure scalar extension carries every component into its corresponding component
of another internal direct sum, it preserves and reflects nonzero components. -/
theorem component_eq_bot_iff_of_tensorEquiv
    (A : ι → Submodule k V) (B : κ → Submodule K W)
    (f : ι → κ) (hf : Function.Injective f)
    (hA : DirectSum.IsInternal A) (hB : DirectSum.IsInternal B)
    (e : K ⊗[k] V ≃ₗ[K] W)
    (he : ∀ i x, x ∈ A i → e (1 ⊗ₜ[k] x) ∈ B (f i)) (i : ι) :
    B (f i) = ⊥ ↔ A i = ⊥ := by
  classical
  constructor
  · intro h
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have hz : e (1 ⊗ₜ[k] x) = 0 := by
      simpa only [h, Submodule.mem_bot] using he i x hx
    have ht : (1 : K) ⊗ₜ[k] x = 0 := e.injective (hz.trans e.map_zero.symm)
    exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff k V x).mp ht
  · intro h
    let q := internalComponentProjection B hB (f i)
    have hq (j : ι) (x : V) (hx : x ∈ A j) :
        q (e (1 ⊗ₜ[k] x)) = 0 := by
      by_cases hj : j = i
      · subst j
        have hx0 : x = 0 := by simpa only [h, Submodule.mem_bot] using hx
        simp [hx0]
      · exact hB.ofBijective_coeLinearMap_of_mem_ne (fun hji => hj (hf hji)) (he j x hx)
    have hqone (x : V) : q (e (1 ⊗ₜ[k] x)) = 0 := by
      have hx : x ∈ ⨆ j, A j := by rw [hA.submodule_iSup_eq_top]; trivial
      refine Submodule.iSup_induction A
        (motive := fun y => q (e (1 ⊗ₜ[k] y)) = 0) hx hq ?_ ?_
      · simp
      · intro x y hx hy
        simp only [TensorProduct.tmul_add, map_add, hx, hy, add_zero]
    have hqall (z : K ⊗[k] V) : q (e z) = 0 := by
      induction z using TensorProduct.inductionOn with
      | tmul c x =>
          have ht : c ⊗ₜ[k] x = c • ((1 : K) ⊗ₜ[k] x) := by
            simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          rw [ht, map_smul, map_smul, hqone, smul_zero]
      | add z z' hz hz' => simp only [map_add, hz, hz', add_zero]
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    have hqy : q y = (⟨y, hy⟩ : B (f i)) :=
      hB.ofBijective_coeLinearMap_of_mem hy
    have hz := hqall (e.symm y)
    rw [e.apply_symm_apply, hqy] at hz
    exact congrArg Subtype.val hz

end Langlands.LinearAlgebra
