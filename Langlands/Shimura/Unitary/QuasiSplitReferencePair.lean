import Langlands.Shimura.Unitary.FiniteModels
import Langlands.Shimura.Unitary.ComplexMatrixSplitting
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.SimpleRing.Matrix

/-! # The quasi-split reference pair on the split CM algebra -/

noncomputable section

universe u v

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global
open scoped TensorProduct

private theorem maxWittAdjoint_entry {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]
    (σ : AlgebraInvolution R C) (n : ℕ) (M : Matrix (Fin n) (Fin n) C) (i j : Fin n) :
    maxWittAdjoint σ n M i j = σ (M j.rev i.rev) := by
  classical
  rw [maxWittAdjoint_formula, Matrix.mul_apply]
  have left (k : Fin n) :
      (maxWittGram C n * matrixTranspose σ n M) i k = σ (M k i.rev) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
    · simp [maxWittGram]
    · intro l _ hl
      simp [maxWittGram, Ne.symm hl]
    · simp
  simp_rw [left]
  rw [Finset.sum_eq_single j.rev]
  · simp [maxWittGram]
  · intro k _ hk
    have hrev : k.rev ≠ j := fun h => hk (by simpa using congrArg Fin.rev h)
    simp [maxWittGram, hrev]
  · simp

variable (E : Type u) (K : Type v)
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]

/-- The split CM matrix algebra with the adjoint of the maximal-Witt Gram matrix. -/
def quasiSplitReferencePair (n : ℕ) (hn : 1 < n) :
    CentralSimpleUnitaryData E K (Matrix (Fin n) (Fin n) K) n := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine
    { involution := maxWittAdjoint (centerInvolution E K) n
      onCenter := ?_
      rank_gt_one := hn
      central := inferInstance
      simple := inferInstance
      finite := inferInstance
      dimension := by simp [Module.finrank_matrix, pow_two] }
  intro k
  ext i j
  rw [maxWittAdjoint_entry]
  change centerInvolution E K (Matrix.scalar (Fin n) k j.rev i.rev) =
    Matrix.scalar (Fin n) (cmConjugation E K k) i j
  by_cases h : i = j
  · subst j
    simp [Matrix.scalar_apply]
    rfl
  · have hrev : j.rev ≠ i.rev := fun he => h (by simpa using (congrArg Fin.rev he).symm)
    simp [Matrix.scalar_apply, h, hrev]

/-- Base change of the reference pair gives the actual maximal-Witt chart,
with the prescribed map of the completed quadratic center. -/
theorem quasiSplitReferencePair_isQuasiSplitAt (n : ℕ) (hn : 1 < n)
    (p : Langlands.Global.FinitePlace E) :
    IsQuasiSplitAt (quasiSplitReferencePair E K n hn).toSecondKindInvolution n p := by
  refine ⟨ComplexMatrix.tensorAlgEquiv E (FiniteCompletion E p) K n, ?_, ?_⟩
  · intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s k =>
      simp only [localCenterMap_tmul, ComplexMatrix.tensorAlgEquiv_tmul]
      ext i j
      change s ⊗ₜ[E] (Matrix.scalar (Fin n) k i j) = _
      by_cases h : i = j <;> simp [Matrix.scalar_apply, h]
  · intro x
    induction x using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul s M =>
      simp only [localInvolution_tmul, ComplexMatrix.tensorAlgEquiv_tmul]
      ext i j
      let N : Matrix (Fin n) (Fin n) (LocalCenter E K p) := fun a b ↦ s ⊗ₜ[E] M a b
      change s ⊗ₜ[E] maxWittAdjoint (centerInvolution E K) n M i j =
        maxWittAdjoint (localConjugation E K p) n N i j
      calc
        _ = s ⊗ₜ[E] centerInvolution E K (M j.rev i.rev) :=
          congrArg (fun k : K ↦ s ⊗ₜ[E] k) (maxWittAdjoint_entry (centerInvolution E K) n M i j)
        _ = localConjugation E K p (N j.rev i.rev) := rfl
        _ = _ := (maxWittAdjoint_entry (localConjugation E K p) n N i j).symm

end Langlands.Shimura.FiniteUnitary
