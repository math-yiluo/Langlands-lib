import Langlands.Shimura.Unitary.ComplexMatrixCoefficients
import Langlands.Shimura.Unitary.ComplexCocharacter

noncomputable section
open Algebra Module
open scoped TensorProduct Classical
attribute [local instance 1100] Algebra.toModule

namespace Langlands.Shimura.ComplexMatrix

variable (S : Type*) [CommRing S]

/-- The corrected Harris pair of diagonal matrices in ordered split coordinates. -/
def splitDiagonal (n r : ℕ) (p : S × S) :
    Matrix (Fin n) (Fin n) S × Matrix (Fin n) (Fin n) S :=
  (Matrix.diagonal (fun i => if i.val < r then p.2 else p.1),
   Matrix.diagonal (fun i => if i.val < r then p.1 else p.2))

end Langlands.Shimura.ComplexMatrix

namespace Langlands.Shimura.HarrisSignatureCharts

universe u v w z
open NumberField
variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {σ : SecondKindInvolution E K A} {n : ℕ}
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts σ n Φ)
  {ι : Type z} [Fintype ι] (b : Basis ι E A)
  (S : Type*) [CommRing S] [Algebra ℂ S] [Algebra ℝ S] [IsScalarTower ℝ ℂ S]

/-- The scalar-extended corrected Harris map has the ordered split diagonal formula. -/
theorem deligneAlgebraMap_matrix (q : DeligneTorus.Complexification S) (τ : E →+* ℝ) :
    C.iteratedScalarMatrixEquiv b S ((C.realComplexHom b).deligneAlgebraMap S q) τ =
      ComplexMatrix.splitDiagonal S n (if τ = C.distinguished then n - 1 else n)
        (DeligneTorus.splitEquiv S q) := by
  apply Prod.ext <;> ext i j <;>
    simp only [AlgebraInvolution.ComplexHom.deligneAlgebraMap_apply, map_add,
      Pi.add_apply, iteratedScalarMatrixEquiv_tmul, map_one, Pi.one_apply,
      realComplexHom_matrix, ComplexMatrix.splitDiagonal, correctedComplexHom_apply,
      Prod.fst_add, Prod.snd_add, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul, Matrix.diagonal_apply, Matrix.one_apply, DeligneTorus.splitEquiv_apply]
  all_goals split_ifs <;> simp [Complex.conj_I, sub_eq_add_neg]

/-- On quadratic units the same formula uses the two split scalar units. -/
theorem delignePoints_matrix (q : DeligneTorus.Points S) (τ : E →+* ℝ) :
    C.iteratedScalarMatrixEquiv b S
        (((C.realComplexHom b).delignePoints S q).val.1 : S ⊗[ℝ] (ℝ ⊗[ℚ] A)) τ =
      ComplexMatrix.splitDiagonal S n (if τ = C.distinguished then n - 1 else n)
        (((DeligneTorus.splitPointsEquiv S q).1 : S),
         ((DeligneTorus.splitPointsEquiv S q).2 : S)) :=
  C.deligneAlgebraMap_matrix b S q τ

/-- The first complex factor has weights zero on the positive block and one on the negative block. -/
theorem delignePoints_firstFactor (u : Sˣ) (τ : E →+* ℝ) :
    C.iteratedScalarMatrixEquiv b S
        (((C.realComplexHom b).delignePoints S
          ((DeligneTorus.splitPointsEquiv S).symm (u, 1))).val.1 :
          S ⊗[ℝ] (ℝ ⊗[ℚ] A)) τ =
      ComplexMatrix.splitDiagonal S n (if τ = C.distinguished then n - 1 else n)
        ((u : S), 1) := by
  rw [C.delignePoints_matrix, MulEquiv.apply_symm_apply]
  rfl

/-- The second factor interchanges the two diagonal weight blocks. -/
theorem delignePoints_secondFactor (u : Sˣ) (τ : E →+* ℝ) :
    C.iteratedScalarMatrixEquiv b S
        (((C.realComplexHom b).delignePoints S
          ((DeligneTorus.splitPointsEquiv S).symm (1, u))).val.1 :
          S ⊗[ℝ] (ℝ ⊗[ℚ] A)) τ =
      ComplexMatrix.splitDiagonal S n (if τ = C.distinguished then n - 1 else n)
        (1, (u : S)) := by
  rw [C.delignePoints_matrix, MulEquiv.apply_symm_apply]
  rfl

end Langlands.Shimura.HarrisSignatureCharts
