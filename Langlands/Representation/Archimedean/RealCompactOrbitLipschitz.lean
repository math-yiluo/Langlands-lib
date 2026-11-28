import Langlands.Representation.Archimedean.OrthogonalLocalLogarithm
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Langlands.Representation.Archimedean.SmoothLieActionUnits
import Langlands.Representation.Archimedean.RightKernelOperatorContinuity
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # A uniform Lipschitz estimate for smooth orthogonal orbits -/

noncomputable section

open scoped Manifold Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open DerivativeSmoothVectors

universe uE

local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ
local notation "G" n:max => Langlands.GeneralLinear n ℝ
local notation "O" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "I" n:max => matrixModel ℝ n
local notation "basis" n:max => Matrix.stdBasis ℝ (Fin n) (Fin n)

private def skewProjection (n : ℕ) : M n →ₗ[ℝ] M n :=
  (1 / 2 : ℝ) • (LinearMap.id - (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toLinearMap)

private theorem skewProjection_apply (n : ℕ) (X : M n) :
    skewProjection n X = (1 / 2 : ℝ) • (X - Xᵀ) := rfl

/-- The skew projection of a standard real matrix unit. -/
def realCompactSkewDirection (n : ℕ) (i : Fin n × Fin n) : M n :=
  skewProjection n ((basis n) i)

theorem realCompactSkewDirection_transpose (n : ℕ) (i : Fin n × Fin n) :
    (realCompactSkewDirection n i)ᵀ = -realCompactSkewDirection n i := by
  unfold realCompactSkewDirection
  rw [skewProjection_apply, Matrix.transpose_smul, Matrix.transpose_sub,
    Matrix.transpose_transpose, ← smul_neg, neg_sub]

/-- The orthogonal orbit of a genuine smooth vector is Lipschitz for the inherited matrix norm.
The Lipschitz constant is controlled by the underlying norm and first skew derivatives. -/
def RealCompactOrbitLipschitzStatement : Prop :=
  ∀ (n : ℕ) (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R : G n →* (E →L[ℂ] E)), IsContinuousRepresentation R →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : DerivativeSmoothVectors (I n) R) (x y : O n),
      ‖R (Unitary.toUnits y) (derivativeCLM (I n) R [] v) -
        R (Unitary.toUnits x) (derivativeCLM (I n) R [] v)‖ ≤
      C * (‖derivativeCLM (I n) R [] v‖ +
        ∑ i : Fin n × Fin n, ‖derivativeCLM (I n) R [realCompactSkewDirection n i] v‖) *
        ‖(y : M n) - (x : M n)‖

private theorem firstDirections_bound (n : ℕ) {E : Type uE}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : G n →* (E →L[ℂ] E)) (v : DerivativeSmoothVectors (I n) R) (X : M n) (hX : Xᵀ = -X) :
    ‖derivativeCLM (I n) R [] (operator (I n) R X v)‖ ≤
      (∑ i : Fin n × Fin n, ‖(basis n).coord i |>.toContinuousLinearMap‖) *
        (∑ i : Fin n × Fin n, ‖derivativeCLM (I n) R [realCompactSkewDirection n i] v‖) * ‖X‖ := by
  let b := basis n
  let D := DerivativeSmoothVectors (I n) R
  let T : M n →ₗ[ℝ] E := ((derivativeCLM (I n) R []).toLinearMap.restrictScalars ℝ).comp
    (((LinearMap.applyₗ v) : (D →ₗ[ℂ] D) →ₗ[ℂ] D).restrictScalars ℝ |>.comp (operatorDirection R))
  let C := ∑ i : Fin n × Fin n, ‖(b.coord i).toContinuousLinearMap‖
  let Y := realCompactSkewDirection n
  have hP : skewProjection n X = X := by
    rw [skewProjection_apply, hX, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
    norm_num
  have hExpansion : X = ∑ i : Fin n × Fin n, (b.coord i X) • Y i := by
    calc
      X = skewProjection n X := hP.symm
      _ = skewProjection n (∑ i : Fin n × Fin n, (b.repr X i) • b i) :=
        congrArg (skewProjection n) (b.sum_repr X).symm
      _ = _ := by simp only [map_sum, map_smul, Module.Basis.coord_apply, Y, realCompactSkewDirection, b]
  have hTX : T X = ∑ i : Fin n × Fin n, (b.coord i X) • T (Y i) := by
    simp only [← map_smul, ← map_sum, ← hExpansion]
  have hT (i : Fin n × Fin n) : T (Y i) = derivativeCLM (I n) R [Y i] v :=
    derivativeCoordinates_operator (I n) R [] (Y i) v
  change ‖T X‖ ≤ C * _ * ‖X‖
  rw [hTX]
  calc
    _ ≤ ∑ i : Fin n × Fin n, ‖(b.coord i X) • T (Y i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n × Fin n, (C * ‖X‖) * ‖derivativeCLM (I n) R [Y i] v‖ := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, hT]
      have hi : ‖b.coord i X‖ ≤ C * ‖X‖ := by
        apply ((b.coord i).toContinuousLinearMap).le_of_opNorm_le
        exact Finset.single_le_sum (fun j _ => norm_nonneg
          (b.coord j).toContinuousLinearMap) (Finset.mem_univ i)
      exact mul_le_mul_of_nonneg_right hi (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

private theorem hasDerivAt_compactOrbit (n : ℕ) {E : Type uE}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : G n →* (E →L[ℂ] E)) (hR : IsContinuousRepresentation R)
    (v : DerivativeSmoothVectors (I n) R) (x : O n) (X : M n) (hX : Xᵀ = -X) :
    HasDerivAt (fun s : ℝ => R (Unitary.toUnits (x * InductionStages.expCurve X hX s))
      (derivativeCLM (I n) R [] v))
      (R (Unitary.toUnits x) (derivativeCLM (I n) R [] (operator (I n) R X v))) 0 := by
  let g := Unitary.toUnits x
  let γ (t : ℝ) := Unitary.toUnits (x * InductionStages.expCurve X hX t)
  let c (t : ℝ) := (γ t).val
  have hd : HasDerivAt c ((x : M n) * X) 0 := by
    have h := (ContinuousLinearMap.mulLeftRight ℝ (M n) (x : M n) 1).hasFDerivAt.comp_hasDerivAt 0
      (RealPrincipalSeriesDuality.hasDerivAt_exp_smul_zero X)
    change HasDerivAt (fun t : ℝ => (x : M n) * NormedSpace.exp (t • X)) ((x : M n) * X) 0
    simpa only [Function.comp_def, ContinuousLinearMap.mulLeftRight_apply, mul_one] using h
  have hc : c 0 = g.val := by simp only [c, γ, g, InductionStages.expCurve_zero, mul_one]
  have h := hasDerivAt_unitsChartOrbit R hR g v hd hc
  have hg : (g⁻¹).val * ((x : M n) * X) = X := by
    have hh : (g⁻¹).val * g.val = 1 := g.inv_val
    rw [← mul_assoc, ← show g.val = (x : M n) from rfl, hh, one_mul]
  simp only [hg, c, unitsChartAction_val] at h
  rw [Langlands.Analysis.hasDerivAt_iff_tendsto_slope_tvs] at h ⊢
  let L := (derivativeCLM (I n) R []).restrictScalars ℝ
  exact (L.continuous.continuousAt.tendsto.comp h).congr fun t => by
    simp only [Function.comp_apply, slope_def_module, map_smul, map_sub]
    rfl

set_option maxHeartbeats 800000 in
theorem realCompactOrbitLipschitz : RealCompactOrbitLipschitzStatement.{uE} := by
  intro n E _ _ _ R hR
  obtain ⟨A, hA, hLip⟩ := exists_lipschitz_bound_of_skew_derivatives n
  let f : O n → G n := Unitary.toUnits
  have hf : Continuous f := continuous_unitary_toUnits
  obtain ⟨B, hB, hNorm⟩ := hR.exists_opNorm_le_of_isCompact (isCompact_univ.image hf)
  have hOp (x : O n) : ‖R (Unitary.toUnits x)‖ ≤ B := hNorm _ ⟨x, Set.mem_univ x, rfl⟩
  let W := ∑ i : Fin n × Fin n, ‖((basis n).coord i).toContinuousLinearMap‖
  have hW : 0 ≤ W := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let C := max B (B * W)
  refine ⟨A * C, mul_nonneg hA.le (hB.trans (le_max_left _ _)), fun v x y => ?_⟩
  let e := derivativeCLM (I n) R []
  let q := ∑ i : Fin n × Fin n, ‖derivativeCLM (I n) R [realCompactSkewDirection n i] v‖
  have hq : 0 ≤ q := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let d := R (Unitary.toUnits y) (e v) - R (Unitary.toUnits x) (e v)
  obtain ⟨L, hL, heval⟩ := exists_dual_vector'' ℂ d
  let φ : C(O n, ℂ) := ⟨fun k => L (R (Unitary.toUnits k) (e v)),
    L.continuous.comp (hR.comp (hf.prodMk continuous_const))⟩
  have hφ (k : O n) (u : E) : ‖L (R (Unitary.toUnits k) u)‖ ≤ B * ‖u‖ := by
    exact (L.le_of_opNorm_le hL _).trans (by
      rw [one_mul]
      exact (R (Unitary.toUnits k)).le_of_opNorm_le (hOp k) u)
  have hφnorm : ‖φ‖ ≤ B * ‖e v‖ :=
    (ContinuousMap.norm_le _ (by positivity)).mpr fun k => hφ k (e v)
  have hd₀ : 0 ≤ B * W * q := by positivity
  have hdφ (k : O n) (X : M n) (hX : Xᵀ = -X) : ∃ a : ℂ,
      HasDerivAt (fun s : ℝ => φ (k * InductionStages.expCurve X hX s)) a 0 ∧
        ‖a‖ ≤ (B * W * q) * ‖X‖ := by
    let u := e (operator (I n) R X v)
    refine ⟨L (R (Unitary.toUnits k) u), ?_, ?_⟩
    · exact (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
        (hasDerivAt_compactOrbit n R hR v k X hX)
    · calc
        _ ≤ B * ‖u‖ := hφ k u
        _ ≤ B * (W * q * ‖X‖) := mul_le_mul_of_nonneg_left (firstDirections_bound n R v X hX) hB
        _ = _ := by ring
  have hnorm : ‖φ y - φ x‖ = ‖d‖ := by
    change ‖L (R (Unitary.toUnits y) (e v)) - L (R (Unitary.toUnits x) (e v))‖ = _
    rw [← map_sub, heval, norm_algebraMap', norm_norm]
  change ‖d‖ ≤ A * C * (‖e v‖ + q) * _
  rw [← hnorm]
  refine (hLip φ (B * W * q) hd₀ hdφ x y).trans ?_
  have hC : ‖φ‖ + B * W * q ≤ C * (‖e v‖ + q) := by
    rw [mul_add]
    exact add_le_add (hφnorm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hq)
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hA.le) (norm_nonneg _)).trans_eq
    (by ring)

end Langlands.Archimedean
