import Langlands.GroupScheme.Quaternionic.QuaternionCoefficientDichotomy
import Langlands.GroupScheme.Quaternionic.RankThreeDivisionPureNorm
import Langlands.GroupScheme.Quaternionic.SplitPureNorm
import Langlands.GroupScheme.Rational.NumberFieldPureQuaternionNorm

/-! # Representing the rank-three skew Gram discriminant by a pure quaternion -/

noncomputable section

universe u

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open Langlands.CentralSimple FiniteAlgebraUnits.MatrixPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

section Coefficients

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  (τ : FirstKindInvolution F D) (R : Type u) [Field R] [Algebra F R]
  (H : Matrix (Fin 3) (Fin 3) D)

local notation "H_R" => coefficientEquiv F D R ((1 : R) ⊗ₜ[F] H)

private theorem skew_coefficientEquiv_tmul (hH : τ.matrix (Fin 3) H = -H) :
    (τ.baseChange R).matrix (Fin 3) H_R = -H_R := by
  ext i j
  change τ.baseChange R (H_R j i) = -(H_R i j)
  rw [← τ.coefficientEquiv_baseChange R ((1 : R) ⊗ₜ[F] H) i j,
    FirstKindInvolution.baseChange_tmul, hH, TensorProduct.tmul_neg, _root_.map_neg, Matrix.neg_apply]

omit τ in
private theorem matrixReducedNorm_coefficientEquiv_tmul [FiniteDimensional F D] [Algebra.IsCentral F D] :
    matrixReducedNorm R H_R = algebraMap F R (reducedNorm F (Matrix (Fin 3) (Fin 3) D) F (1 ⊗ₜ[F] H)) := by
  change reducedNorm F (Matrix (Fin 3) (Fin 3) D) R ((coefficientEquiv F D R).symm H_R) =
    (Algebra.ofId F R) (reducedNorm F (Matrix (Fin 3) (Fin 3) D) F (1 ⊗ₜ[F] H))
  rw [AlgEquiv.symm_apply_apply, ← reducedNorm_naturality F (Matrix (Fin 3) (Fin 3) D) (Algebra.ofId F R),
    Algebra.TensorProduct.map_tmul, _root_.map_one]
  rfl

end Coefficients

/-- An invertible rank-three skew-hermitian form over a number-field quaternion
  division algebra has Gram norm represented by a nonzero pure quaternion if it
  represents zero nonsingularly over every completion. -/
def NumberFieldRankThreeGramPureNormStatement : Prop :=
  ∀ (F D : Type u) [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
    [FiniteDimensional F D] [Algebra.IsCentral F D] (σ : FirstKindInvolution F D)
    (hdim : Module.finrank F D = 4) (hsym : Module.finrank F σ.symmetricSubspace = 3),
    let τ := σ.quaternionConjugation hdim hsym
    ∀ (H : Matrix (Fin 3) (Fin 3) D), τ.IsAntihermitian H → IsUnit H →
      (∀ v : Global.Place F, let R := Global.placeCompletion F v
        let M := coefficientEquiv F D R ((1 : R) ⊗ₜ[F] H)
        ∃ (x : Fin 3 → R ⊗[F] D) (i : Fin 3), IsUnit (x i) ∧
          ∑ j, ∑ k, x j * M j k * τ.baseChange R (x k) = 0) →
      ∃ a : D, a ∈ τ.alternatingSubspace ∧ a ≠ 0 ∧
        reducedNorm F D F (1 ⊗ₜ[F] a) = reducedNorm F (Matrix (Fin 3) (Fin 3) D) F (1 ⊗ₜ[F] H)

/-- Split and division places both give local pure norm representatives. Apply
  the ternary norm locality theorem to obtain the global representative. -/
theorem numberFieldRankThreeGramPureNorm : NumberFieldRankThreeGramPureNormStatement.{u} := by
  intro F D _ _ _ _ _ _ σ hdim hsym τ H hH hu hloc
  let a := reducedNorm F (Matrix (Fin 3) (Fin 3) D) F (1 ⊗ₜ[F] H)
  have ha : a ≠ 0 := by
    have hunit : IsUnit ((1 : F) ⊗ₜ[F] H) := hu.map
      (Algebra.TensorProduct.includeRight : Matrix (Fin 3) (Fin 3) D →ₐ[F] F ⊗[F] _)
    exact (hunit.map (reducedNorm F (Matrix (Fin 3) (Fin 3) D) F)).ne_zero
  have localNorm {R : Type u} [Field R] [Algebra F R]
      (h : let M := coefficientEquiv F D R ((1 : R) ⊗ₜ[F] H)
        ∃ (x : Fin 3 → R ⊗[F] D) (i : Fin 3), IsUnit (x i) ∧
          ∑ j, ∑ k, x j * M j k * τ.baseChange R (x k) = 0) :
      ∃ y : R ⊗[F] D, y ∈ (τ.baseChange R).alternatingSubspace ∧
        reducedNorm F D R y = algebraMap F R a := by
    let : CharZero R := charZero_of_injective_algebraMap (algebraMap F R).injective
    let : Invertible (2 : R) := invertibleOfNonzero two_ne_zero
    rcases quaternionCoefficientDichotomy F D R hdim with hdom | he
    · obtain ⟨x, i, hxi, hx⟩ := h
      have hx0 : x ≠ 0 := fun hz => hxi.ne_zero (congrFun hz i)
      let M := coefficientEquiv F D R ((1 : R) ⊗ₜ[F] H)
      have hU : IsUnit M := (hu.map (Algebra.TensorProduct.includeRight :
        Matrix (Fin 3) (Fin 3) D →ₐ[F] R ⊗[F] Matrix (Fin 3) (Fin 3) D)).map (coefficientEquiv F D R)
      have hS : (τ.baseChange R).matrix (Fin 3) M = -M := τ.skew_coefficientEquiv_tmul R H hH.1
      obtain ⟨y, hy, hN⟩ := σ.exists_pureNorm_eq_matrixReducedNorm_of_isotropic hdim hsym hdom M hU hS hx0 hx
      exact ⟨y, hy, hN.trans (matrixReducedNorm_coefficientEquiv_tmul R H)⟩
    · exact σ.exists_alternating_reducedNorm_of_split hdim hsym he.some (algebraMap F R a)
  have hrep (v : Global.Place F) : let R := Global.placeCompletion F v
      ∃ x : R ⊗[F] D, x ∈ (τ.baseChange R).alternatingSubspace ∧ reducedNorm F D R x = algebraMap F R a := by
    rcases v with v | v
    · exact localNorm (R := v.Completion) (hloc (.inl v))
    · exact localNorm (R := Global.FiniteCompletion F v) (hloc (.inr v))
  obtain ⟨z, hz, hzN⟩ := numberFieldPureQuaternionNorm F D σ hdim hsym a hrep
  refine ⟨z, hz, fun h0 => ha ?_, hzN⟩
  rw [← hzN, h0, TensorProduct.tmul_zero, _root_.map_zero]

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
