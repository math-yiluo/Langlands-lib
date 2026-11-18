import Langlands.GroupScheme.SimplyConnected.NormOneGaloisConjugators
import Mathlib.LinearAlgebra.TensorProduct.Opposite

/-! # Transpose charts and the opposite algebra in norm-one descent -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.CentralSimpleUnits.TitsDescent

variable {k L A : Type u} [Field k] [Field L] [Algebra k L]
    [Ring A] [Algebra k A]
    {I : Type} [Fintype I] [DecidableEq I]

/-- Scalar extension commutes with the opposite algebra, keeping the commutative field factor. -/
def scalarOppositeEquiv : L ⊗[k] Aᵐᵒᵖ ≃ₐ[L] (L ⊗[k] A)ᵐᵒᵖ :=
  (Algebra.TensorProduct.congr (AlgEquiv.toOpposite L L)
    (AlgEquiv.refl : Aᵐᵒᵖ ≃ₐ[k] Aᵐᵒᵖ)).trans
      (Algebra.TensorProduct.opAlgEquiv k L L A)

@[simp] theorem scalarOppositeEquiv_tmul (l : L) (a : A) :
    scalarOppositeEquiv (l ⊗ₜ[k] MulOpposite.op a) = MulOpposite.op (l ⊗ₜ[k] a) := rfl

variable (e : L ⊗[k] A ≃ₐ[L] Matrix I I L)

/-- The original algebra chart gives the transpose chart of the actual opposite algebra. -/
def oppositeChart : L ⊗[k] Aᵐᵒᵖ ≃ₐ[L] Matrix I I L :=
  ((scalarOppositeEquiv (k := k) (L := L) (A := A)).trans (AlgEquiv.op e)).trans
    (Matrix.transposeAlgEquiv (m := I) (R := L) (α := L)).symm

@[simp] theorem oppositeChart_tmul (l : L) (a : A) :
    oppositeChart e (l ⊗ₜ[k] MulOpposite.op a) = (e (l ⊗ₜ[k] a))ᵀ := rfl

/-- The inverse transpose of the original Galois conjugator is the dual conjugator. -/
def dualConjugator (σ : L ≃ₐ[k] L) : (Matrix I I L)ˣ where
  val := (((galoisConjugator e σ)⁻¹ : (Matrix I I L)ˣ) : Matrix I I L)ᵀ
  inv := (galoisConjugator e σ : Matrix I I L)ᵀ
  val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

/-- This inverse transpose intertwines the actual transposed constant matrices. -/
theorem dualConjugator_constant (σ : L ≃ₐ[k] L) (a : A) :
    (dualConjugator e σ : Matrix I I L) * oppositeChart e (1 ⊗ₜ[k] MulOpposite.op a) =
      (oppositeChart e (1 ⊗ₜ[k] MulOpposite.op a)).map σ *
        (dualConjugator e σ : Matrix I I L) := by
  rw [oppositeChart_tmul]
  have ht := congrArg Matrix.transpose (galoisConjugator_constant e σ a)
  simp only [Matrix.transpose_mul] at ht
  change (e (1 ⊗ₜ[k] a))ᵀ * ((dualConjugator e σ)⁻¹ : (Matrix I I L)ˣ) =
    ((dualConjugator e σ)⁻¹ : (Matrix I I L)ˣ) * ((e (1 ⊗ₜ[k] a)).map σ)ᵀ at ht
  have h := congrArg (fun M : Matrix I I L => M * (dualConjugator e σ : Matrix I I L)) ht
  simp only [mul_assoc, Units.inv_mul, mul_one] at h
  have h' := congrArg (fun M : Matrix I I L => (dualConjugator e σ : Matrix I I L) * M) h
  simpa only [← mul_assoc, Units.mul_inv, one_mul, Matrix.transpose_map] using h'

section Galois

variable [IsGalois k L]

/-- Transpose identifies the opposite of the original descended algebra with
the actual fixed algebra from the opposite chart. -/
def oppositeFixedEquiv :
    ((matrixAction e).fixed)ᵐᵒᵖ ≃ₐ[k] (matrixAction (oppositeChart e)).fixed :=
  (AlgEquiv.op (fixedEquivOfIsGalois e)).symm.trans
    (fixedEquivOfIsGalois (oppositeChart e))

theorem oppositeFixedEquiv_val (X : ((matrixAction e).fixed)ᵐᵒᵖ) :
    (oppositeFixedEquiv e X : Matrix I I L) = (X.unop : Matrix I I L)ᵀ := by
  obtain ⟨a, rfl⟩ := (AlgEquiv.op (fixedEquivOfIsGalois e)).surjective X
  simp only [oppositeFixedEquiv, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  change (fixedEquivOfIsGalois (oppositeChart e) a : Matrix I I L) =
    (fixedEquivOfIsGalois e a.unop : Matrix I I L)ᵀ
  rw [fixedEquivOfIsGalois_val, fixedEquivOfIsGalois_val]
  exact oppositeChart_tmul e 1 a.unop

/-- The actual descended algebra associated to the transpose chart is the original opposite. -/
def originalOppositeFixedEquiv : Aᵐᵒᵖ ≃ₐ[k] (matrixAction (oppositeChart e)).fixed :=
  fixedEquivOfIsGalois (oppositeChart e)

@[simp] theorem originalOppositeFixedEquiv_val (a : A) :
    (originalOppositeFixedEquiv e (MulOpposite.op a) : Matrix I I L) =
      (e (1 ⊗ₜ[k] a))ᵀ := rfl

end Galois

end Langlands.GroupScheme.CentralSimpleUnits.TitsDescent
