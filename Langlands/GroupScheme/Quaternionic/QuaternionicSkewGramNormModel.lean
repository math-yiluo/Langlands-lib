import Langlands.GroupScheme.Quaternionic.QuaternionicPureFactorization
import Langlands.GroupScheme.Quaternionic.SkewHermitianOrthogonalBasis
import Langlands.GroupScheme.Quaternionic.HyperbolicBasis

/-! # Rank-three skew Gram models with matching reduced norm -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open Langlands.CentralSimple FiniteAlgebraUnits.MatrixPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  [Algebra.IsCentral F D] [FiniteDimensional F D]

private theorem reducedNorm_mul_sq_eq_norm_prod (τ : FirstKindInvolution F D)
    {H : Matrix (Fin 3) (Fin 3) D} (hH : τ.IsAntihermitian H) (hu : IsUnit H)
    (hτ : ∃ a, τ a ≠ a) :
    ∃ (p : F) (a : D), p ≠ 0 ∧ a ≠ 0 ∧
      reducedNorm F (Matrix (Fin 3) (Fin 3) D) F (1 ⊗ₜ[F] H) * p ^ 2 =
        reducedNorm F D F (1 ⊗ₜ[F] a) := by
  let B := AntihermitianForm.ofMatrix hH
  obtain ⟨b, hb, hd⟩ := AntihermitianForm.orthogonalBasis F D τ (Fin 3 → D) B hτ
    (AntihermitianForm.ofMatrix_separatingLeft hH hu)
  let e : Fin (Module.finrank D (Fin 3 → D)) ≃ Fin 3 := finCongr (Module.finrank_fin_fun D)
  let c := b.reindex e
  let v : Fin 3 → D := fun i => B (c i) (c i)
  have hv (i : Fin 3) : v i ≠ 0 := by
    simpa only [v, c, Module.Basis.reindex_apply] using hd (e.symm i)
  let P : Matrix (Fin 3) (Fin 3) D := Matrix.of c
  have hP : P * H * τ.matrix (Fin 3) P = Matrix.diagonal v := by
    ext i j
    rw [τ.mul_mul_matrix_apply, Matrix.diagonal_apply]
    change B (c i) (c j) = _
    by_cases h : i = j
    · subst j
      rw [ite_eq_left rfl]
    · rw [ite_eq_right h]
      simp only [c, Module.Basis.reindex_apply]
      exact hb _ _ (fun he => h (e.symm.injective he))
  have hPu := τ.isUnit_of_mul_mul_matrix_eq
    ((Pi.isUnit_iff.mpr (fun i => isUnit_iff_ne_zero.mpr (hv i))).map
      (Matrix.diagonalRingHom (Fin 3) D)) hP
  let j : D →ₐ[F] F ⊗[F] D := Algebra.TensorProduct.includeRight
  let J := j.mapMatrix (m := Fin 3)
  have hJ (X : Matrix (Fin 3) (Fin 3) D) : J X = coefficientEquiv F D F ((1 : F) ⊗ₜ[F] X) := by
    ext i k
    rw [coefficientEquiv_tmul]
    rfl
  have hJadj : J (τ.matrix (Fin 3) P) = (τ.baseChange F).matrix (Fin 3) (J P) := by
    ext i k
    rw [hJ, hJ, FirstKindInvolution.matrix_apply, coefficientEquiv_tmul, coefficientEquiv_tmul,
      FirstKindInvolution.matrix_apply, FirstKindInvolution.baseChange_tmul]
  have hJdiag : J (Matrix.diagonal v) = Matrix.diagonal (fun i => (1 : F) ⊗ₜ[F] v i) :=
    Matrix.diagonal_map (_root_.map_zero j)
  have hNH : matrixReducedNorm F (J H) =
      reducedNorm F (Matrix (Fin 3) (Fin 3) D) F (1 ⊗ₜ[F] H) := by
    rw [hJ]
    change reducedNorm F (Matrix (Fin 3) (Fin 3) D) F
      ((coefficientEquiv F D F).symm (coefficientEquiv F D F ((1 : F) ⊗ₜ[F] H))) = _
    rw [AlgEquiv.symm_apply_apply]
  refine ⟨matrixReducedNorm F (J P), v 0 * v 1 * v 2,
    ((hPu.map J).map (matrixReducedNorm F)).ne_zero, mul_ne_zero (mul_ne_zero (hv 0) (hv 1)) (hv 2), ?_⟩
  rw [← hNH, ← matrixReducedNorm_congruence F τ, ← hJadj, ← _root_.map_mul,
    ← _root_.map_mul, hP, hJdiag, matrixReducedNorm_diagonal, Fin.prod_univ_three]
  let N := reducedNorm F D F
  change N (j (v 0)) * N (j (v 1)) * N (j (v 2)) = N (j (v 0 * v 1 * v 2))
  rw [← _root_.map_mul, ← _root_.map_mul, ← _root_.map_mul j, ← _root_.map_mul j]

/-- An invertible rank-three skew Gram matrix has the same reduced norm as
  an invertible diagonal skew Gram matrix with any prescribed nonzero pure first entry. -/
def QuaternionicRankThreeMatchedNormModelStatement : Prop :=
  ∀ (F D : Type u) [Field F] [DivisionRing D] [Algebra F D]
    [Algebra.IsCentral F D] [FiniteDimensional F D] [Invertible (2 : F)]
    (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
    (hsym : Module.finrank F σ.symmetricSubspace = 3),
    let τ := σ.quaternionConjugation hdim hsym
    ∀ (H : Matrix (Fin 3) (Fin 3) D), τ.IsAntihermitian H → IsUnit H →
    ∀ c : D, c ∈ τ.alternatingSubspace → c ≠ 0 →
    ∃ d e : D, let M := Matrix.diagonal ![c, d, e]
      τ.IsAntihermitian M ∧ IsUnit M ∧
        reducedNorm F (Matrix (Fin 3) (Fin 3) D) F (1 ⊗ₜ[F] M) =
          reducedNorm F (Matrix (Fin 3) (Fin 3) D) F (1 ⊗ₜ[F] H)

theorem quaternionicRankThreeMatchedNormModel : QuaternionicRankThreeMatchedNormModelStatement.{u} := by
  intro F D _ _ _ _ _ _ σ hdim hsym τ H hH hu c hc hc0
  have hτ : ∃ a, τ a ≠ a := by
    refine ⟨c, fun h => smul_ne_zero (isUnit_of_invertible (2 : F)).ne_zero hc0 ?_⟩
    rw [two_smul]
    exact (congrArg (fun z : D => z + c) (h.symm.trans (τ.map_eq_neg_of_mem_alternating hc))).trans
      (neg_add_cancel _)
  obtain ⟨p, b, hp, hb, hN⟩ := reducedNorm_mul_sq_eq_norm_prod τ hH hu hτ
  let a := p⁻¹ • (b * c⁻¹)
  have ha : a ≠ 0 := smul_ne_zero (inv_ne_zero hp) (mul_ne_zero hb (inv_ne_zero hc0))
  obtain ⟨d, e, hM, hMu, hMN⟩ := quaternionicRankThreeNormModel F D σ hdim hsym c a hc hc0 ha
  have hca : a * c = p⁻¹ • b := by
    rw [show a = p⁻¹ • (b * c⁻¹) from rfl, smul_mul_assoc, mul_assoc,
      inv_mul_cancel₀ hc0, mul_one]
  refine ⟨d, e, hM, hMu, hMN.trans ?_⟩
  let N := reducedNorm F D F
  change N (1 ⊗ₜ[F] c) * N (1 ⊗ₜ[F] a) = _
  rw [mul_comm, ← _root_.map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hca]
  have htensor : (1 : F) ⊗ₜ[F] (p⁻¹ • b) = (p⁻¹ ⊗ₜ[F] (1 : D)) * ((1 : F) ⊗ₜ[F] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← TensorProduct.smul_tmul,
      smul_eq_mul, mul_one]
  rw [htensor, _root_.map_mul, show N (p⁻¹ ⊗ₜ[F] (1 : D)) = (p⁻¹) ^ 2 from by
      rw [show N = reducedNorm F D F from rfl, reducedNorm_scalar,
        reducedDegree_eq_two_of_finrank_four hdim], ← hN, mul_left_comm, ← mul_pow,
    inv_mul_cancel₀ hp, one_pow, mul_one]

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
