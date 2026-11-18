import Langlands.Algebra.GaloisAlgebraDescent
import Mathlib.FieldTheory.Galois.Infinite

/-! # Noncommutative fixed tensors over arbitrary Galois extensions -/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Langlands.GaloisAlgebraDescent

variable (k : Type u) [Field k] (L : Type v) [Field L] [Algebra k L] [IsGalois k L]
    (A : Type w) [Ring A] [Algebra k A]

/-- Fixed tensors lie in the original algebra for any Galois extension,
without finite-dimensionality of the field extension or the algebra. -/
theorem mem_range_includeRight_iff_of_isGalois (x : L ⊗[k] A) :
    x ∈ (Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A).range ↔
      ∀ σ : L ≃ₐ[k] L, coefficientConjugate k L A σ x = x := by
  classical
  constructor
  · rintro ⟨a, rfl⟩ σ
    simp [Algebra.TensorProduct.includeRight_apply]
  · intro hx
    let b := Module.Free.chooseBasis k A
    let v := (b.baseChange L).repr x
    have hv : ∀ i, v i ∈ Set.range (algebraMap k L) := by
      intro i
      apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
      intro σ
      change σ ((b.baseChange L).repr x i) = (b.baseChange L).repr x i
      rw [← repr_coefficientConjugate, hx σ]
    choose c hc using hv
    refine ⟨∑ i ∈ v.support, c i • b i, ?_⟩
    change (Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A)
      (∑ i ∈ v.support, c i • b i) = x
    calc
      _ = ∑ i ∈ v.support, v i • (b.baseChange L) i := by
        simp only [map_sum, map_smul]
        apply Finset.sum_congr rfl
        intro i _
        rw [← hc i, Module.Basis.baseChange_apply]
        simp [Algebra.TensorProduct.includeRight_apply, Algebra.smul_def]
      _ = x := by
        simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
          (b.baseChange L).linearCombination_repr x

end Langlands.GaloisAlgebraDescent
