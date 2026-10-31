import Langlands.Shimura.PEL.HodgeDeterminantReflex
import Langlands.Shimura.Unitary.CocharacterReflexConjugator
import Mathlib.LinearAlgebra.Trace

/-! # Central traces on the actual regular Kottwitz Hodge module -/

noncomputable section
open NumberField _root_.Algebra Module
open scoped TensorProduct Classical

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
    (hΦ : IsCMSection E K Φ)

/-- Embedding-labelled matrices of the actual iterated complex tensor algebra. -/
def kottwitzHodgeMatrixEquiv :
    ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A) ≃ₐ[ℂ] ((K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) :=
  (AlgebraInvolution.baseChangeTowerEquiv ℚ ℝ ℂ A).symm.trans
    (C.embeddingMatrixEquiv hΦ D.totallyRealBasis)

/-- Right multiplication selects columns of every actual embedding matrix. -/
theorem mem_kottwitzHodgeModule_iff_columns (x : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)) :
    x ∈ D.kottwitzHodgeModule C ↔
      ∀ (i : K →+* ℂ) (r c : Fin n),
        ¬ D.kottwitzEmbeddingSupport C hΦ i c →
          D.kottwitzHodgeMatrixEquiv C hΦ x i r c = 0 := by
  have hdiag (u : ℂˣ) (i : K →+* ℂ) :
      C.embeddingMatrixEquiv hΦ D.totallyRealBasis
          (D.kottwitzCocharacterUnit C u : ℂ ⊗[ℚ] A) i =
        Matrix.diagonal (fun j => if D.kottwitzEmbeddingSupport C hΦ i j
          then (↑(u⁻¹) : ℂ) else 1) :=
    D.kottwitzCocharacterValue_diagonal C hΦ i u
  rw [D.mem_kottwitzHodgeModule_iff C]
  constructor
  · intro hx i r c hc
    have h := congrArg
      (fun y : ℂ ⊗[ℚ] A => C.embeddingMatrixEquiv hΦ D.totallyRealBasis y i r c)
      (hx (-1))
    simp only [map_mul, Pi.mul_apply,
      hdiag,
      Matrix.mul_diagonal, hc, ite_false, mul_one, inv_neg, inv_one,
      Units.val_neg, Units.val_one, neg_one_smul, map_neg, Pi.neg_apply,
      Matrix.neg_apply] at h
    change D.kottwitzHodgeMatrixEquiv C hΦ x i r c = 0
    change D.kottwitzHodgeMatrixEquiv C hΦ x i r c =
      - D.kottwitzHodgeMatrixEquiv C hΦ x i r c at h
    linear_combination h / 2
  · intro hx u
    apply (C.embeddingMatrixEquiv hΦ D.totallyRealBasis).injective
    ext i r c
    simp only [map_mul, map_smul, Pi.mul_apply,
      hdiag,
      Matrix.mul_diagonal, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases hc : D.kottwitzEmbeddingSupport C hΦ i c
    · simp [hc, mul_comm]
    · have hz := hx i r c hc
      change C.embeddingMatrixEquiv hΦ D.totallyRealBasis
        ((AlgebraInvolution.baseChangeTowerEquiv ℚ ℝ ℂ A).symm x) i r c = 0 at hz
      simp [hc, hz]

/-- One coordinate for every row and selected column of every CM matrix factor. -/
def KottwitzHodgeCoordinateIndex :=
  Σ i : K →+* ℂ, Fin n × {j : Fin n // D.kottwitzEmbeddingSupport C hΦ i j}

instance fintypeKottwitzHodgeCoordinateIndex :
    Fintype (D.KottwitzHodgeCoordinateIndex C hΦ) := by
  unfold KottwitzHodgeCoordinateIndex
  infer_instance

/-- Actual Hodge vectors are exactly arbitrary values on the selected matrix coordinates. -/
def kottwitzHodgeCoordinateEquiv :
    D.kottwitzHodgeModule C ≃ₗ[ℂ] (D.KottwitzHodgeCoordinateIndex C hΦ → ℂ) where
  toFun x q := D.kottwitzHodgeMatrixEquiv C hΦ x q.1 q.2.1 q.2.2.1
  invFun f :=
    ⟨(D.kottwitzHodgeMatrixEquiv C hΦ).symm
      (fun i r c => if hc : D.kottwitzEmbeddingSupport C hΦ i c
        then f ⟨i, r, ⟨c, hc⟩⟩ else 0), by
      rw [D.mem_kottwitzHodgeModule_iff_columns C hΦ]
      intro i r c hc
      simp [hc]⟩
  left_inv x := by
    apply Subtype.ext
    apply (D.kottwitzHodgeMatrixEquiv C hΦ).injective
    ext i r c
    simp only [AlgEquiv.apply_symm_apply]
    split_ifs with hc
    · rfl
    · exact ((D.mem_kottwitzHodgeModule_iff_columns C hΦ x).mp x.2 i r c hc).symm
  right_inv f := by
    funext q
    rcases q with ⟨i, r, c, hc⟩
    simp only [AlgEquiv.apply_symm_apply, dite_eq_left hc]
  map_add' x y := by
    funext q
    exact congrArg (fun M => M q.1 q.2.1 q.2.2.1)
      (map_add (D.kottwitzHodgeMatrixEquiv C hΦ)
        (x : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)) (y : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)))
  map_smul' z x := by
    funext q
    exact congrArg (fun M => M q.1 q.2.1 q.2.2.1)
      (map_smul (D.kottwitzHodgeMatrixEquiv C hΦ) z
        (x : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)))

/-- The centre acts at each actual Hodge coordinate through its labelled embedding. -/
theorem kottwitzHodgeCoordinateEquiv_center (a : K) (x : D.kottwitzHodgeModule C)
    (q : D.KottwitzHodgeCoordinateIndex C hΦ) :
    D.kottwitzHodgeCoordinateEquiv C hΦ
        (D.kottwitzHodgeAction C
          ((1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] algebraMap K A a)) x) q =
      q.1 a * D.kottwitzHodgeCoordinateEquiv C hΦ x q := by
  change D.kottwitzHodgeMatrixEquiv C hΦ
      (((1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] algebraMap K A a)) * (x : _))
        q.1 q.2.1 q.2.2.1 = _
  rw [map_mul]
  change (C.embeddingMatrixEquiv hΦ D.totallyRealBasis
    ((AlgebraInvolution.baseChangeTowerEquiv ℚ ℝ ℂ A).symm
      ((1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] algebraMap K A a))) q.1 *
      D.kottwitzHodgeMatrixEquiv C hΦ x q.1) q.2.1 q.2.2.1 = _
  rw [AlgebraInvolution.baseChangeTowerEquiv_symm_tmul, one_smul,
    C.embeddingMatrixEquiv_tmul, one_smul,
    C.embeddingEvaluation_center hΦ D.totallyRealBasis, Matrix.scalar_apply,
    Matrix.diagonal_mul]
  rfl

/-- The intrinsic trace on the actual Hodge module is the sum of its central coordinates. -/
theorem trace_kottwitzHodgeAction_center_coordinates (a : K) :
    LinearMap.trace ℂ (D.kottwitzHodgeModule C)
      (D.kottwitzHodgeAction C
        ((1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] algebraMap K A a))) =
      ∑ q : D.KottwitzHodgeCoordinateIndex C hΦ, q.1 a := by
  let e := D.kottwitzHodgeCoordinateEquiv C hΦ
  rw [← LinearMap.trace_conj' _ e,
    LinearMap.trace_eq_matrix_trace ℂ
      (Pi.basisFun ℂ (D.KottwitzHodgeCoordinateIndex C hΦ)), Matrix.trace]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr,
    LinearEquiv.conj_apply_apply]
  change e (D.kottwitzHodgeAction C
    ((1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] algebraMap K A a))
      (e.symm ((Pi.basisFun ℂ (D.KottwitzHodgeCoordinateIndex C hΦ)) q))) q = _
  rw [D.kottwitzHodgeCoordinateEquiv_center C hΦ]
  change q.1 a * e (e.symm _) q = _
  rw [e.apply_symm_apply]
  simp

include hΦ in
/-- Each selected column contributes all `n` rows to the actual central trace. -/
theorem trace_kottwitzHodgeAction_center (a : K) :
    LinearMap.trace ℂ (D.kottwitzHodgeModule C)
      (D.kottwitzHodgeAction C
        ((1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] algebraMap K A a))) =
      (n : ℂ) * ∑ i : K →+* ℂ, (D.realHodgeFunction C i : ℂ) * i a := by
  have hc (i : K →+* ℂ) :
      Fintype.card {j : Fin n // D.kottwitzEmbeddingSupport C hΦ i j} =
        D.realHodgeFunction C i := by
    rw [Fintype.card_subtype, D.card_kottwitzEmbeddingSupport C hΦ]
  rw [D.trace_kottwitzHodgeAction_center_coordinates C hΦ]
  change (∑ q : Σ i : K →+* ℂ,
    Fin n × {j : Fin n // D.kottwitzEmbeddingSupport C hΦ i j}, q.1 a) = _
  rw [Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [hc, nsmul_eq_mul, mul_assoc]

end Langlands.Shimura.CentralSimpleUnitaryData
