import Langlands.Representation.Archimedean.ComplexJacquetOrbit
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# A chart of the matrices at the identity adapted to `B · U(n)`

Every complex `n × n` matrix `X` splits as `X = P_b X + P_u X`, where
`P_u X = L − Lᴴ + i Im diag(X)` is skew-Hermitian (`L` the strictly lower triangular part of
`X`) and `P_b X = X − P_u X` is upper triangular with real diagonal. The map
`Φ(X) = (1 + P_b X) exp(P_u X)` is `C^∞`, sends `0` to `1` and has derivative the identity at
`0`. By the inverse function theorem it has a `C^∞` local inverse `Ψ` at `1`
(`exists_chartInverse`): near `1` every matrix is `(1 + P_b Ψ(y)) exp(P_u Ψ(y))`, an upper
triangular matrix with nonzero diagonal entries times a unitary matrix, with both factors
`C^∞` in `y`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ContDiff Topology

set_option autoImplicit false

namespace Langlands.Archimedean

-- As in `GeneralLinear`: the operator norm on matrices needs reduction through the
-- normed-ring instances.
set_option backward.isDefEq.respectTransparency false

section Chart

variable {n : ℕ}

/-- The skew-Hermitian part `L − Lᴴ + i Im diag(X)` of `X`, where `L` is the strictly lower
triangular part of `X`. -/
def skewPart : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := Matrix.of fun i j =>
    if j < i then X i j else if i < j then -star (X j i) else ((X i i).im : ℂ) * Complex.I
  map_add' X Y := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, star_add, neg_add, Complex.add_im,
      Complex.ofReal_add, add_mul]
    split_ifs <;> rfl
  map_smul' r X := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]
    split_ifs
    · rfl
    · rw [star_smul, star_trivial, smul_neg]
    · rw [Complex.smul_im, smul_eq_mul, Complex.real_smul]
      push_cast
      ring

theorem skewPart_apply (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    skewPart X i j =
      if j < i then X i j else if i < j then -star (X j i) else ((X i i).im : ℂ) * Complex.I :=
  rfl

/-- `P_u X` is skew-Hermitian. -/
theorem star_skewPart (X : Matrix (Fin n) (Fin n) ℂ) : star (skewPart X) = -skewPart X := by
  ext i j
  rw [Matrix.star_apply, Matrix.neg_apply, skewPart_apply, skewPart_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, not_lt_of_gt h]
  · simp
  · simp [h, not_lt_of_gt h]

/-- The upper triangular part `P_b X = X − P_u X`, with real diagonal. -/
def upperPart : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.id - skewPart

theorem upperPart_add_skewPart (X : Matrix (Fin n) (Fin n) ℂ) :
    upperPart X + skewPart X = X := by
  simp [upperPart]

theorem upperPart_apply (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    upperPart X i j = X i j - skewPart X i j :=
  rfl

theorem upperPart_isUpperTriangular (X : Matrix (Fin n) (Fin n) ℂ) :
    (upperPart X).IsUpperTriangular := by
  intro i j h
  have h' : j < i := h
  rw [upperPart_apply, skewPart_apply]
  simp [h']

theorem upperPart_diag (X : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    upperPart X j j = ((X j j).re : ℂ) := by
  rw [upperPart_apply, skewPart_apply]
  apply Complex.ext <;> simp

/-- The upper triangular factor `1 + P_b X` of the chart. -/
theorem one_add_upperPart_isUpperTriangular (X : Matrix (Fin n) (Fin n) ℂ) :
    (1 + upperPart X).IsUpperTriangular :=
  Matrix.blockTriangular_one.add (upperPart_isUpperTriangular X)

/-- The chart `Φ(X) = (1 + P_b X) exp(P_u X)`. -/
def chart (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 + upperPart X) * NormedSpace.exp (skewPart X)

theorem chart_zero : chart (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  simp [chart]

theorem contDiff_chart : ContDiff ℝ ∞ (chart (n := n)) := by
  have hU : ContDiff ℝ ∞ (fun X : Matrix (Fin n) (Fin n) ℂ => upperPart X) :=
    (LinearMap.toContinuousLinearMap upperPart).contDiff
  have hS : ContDiff ℝ ∞ (fun X : Matrix (Fin n) (Fin n) ℂ => skewPart X) :=
    (LinearMap.toContinuousLinearMap skewPart).contDiff
  exact (contDiff_const.add hU).mul ((contDiff_matrix_exp n).comp hS)

/-- The derivative of the chart at `0` is the identity. -/
theorem hasFDerivAt_chart :
    HasFDerivAt (chart (n := n)) (ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℂ)) 0 := by
  set U := LinearMap.toContinuousLinearMap (upperPart (n := n)) with hU
  set S := LinearMap.toContinuousLinearMap (skewPart (n := n)) with hS
  have ha : HasFDerivAt (fun X : Matrix (Fin n) (Fin n) ℂ => 1 + upperPart X) U 0 :=
    U.hasFDerivAt.const_add 1
  have he : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (S 0) := by
    rw [map_zero]
    exact hasFDerivAt_exp_zero
  have hb : HasFDerivAt (fun X : Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp (skewPart X))
      ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ).comp S) 0 :=
    he.comp 0 S.hasFDerivAt
  have h := ha.fun_mul' hb
  refine h.congr_fderiv ?_
  ext1 X
  simp [hU, hS, add_comm (skewPart X), upperPart_add_skewPart]

/-- **The local inverse of the chart.** There is a `C^∞` map `Ψ` near `1` with `Ψ(1) = 0`,
`Ψ(y) → 0` as `y → 1`, and `Φ(Ψ(y)) = y` for `y` near `1`. -/
theorem exists_chartInverse :
    ∃ Ψ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
      ContDiffAt ℝ ∞ Ψ 1 ∧ Ψ 1 = 0 ∧ Filter.Tendsto Ψ (𝓝 1) (𝓝 0) ∧
        ∀ᶠ y in 𝓝 1, chart (Ψ y) = y := by
  have hc : ContDiffAt ℝ ∞ (chart (n := n)) 0 := contDiff_chart.contDiffAt
  have hd : HasFDerivAt (chart (n := n))
      ((ContinuousLinearEquiv.refl ℝ (Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ)) 0 :=
    hasFDerivAt_chart
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hs := hc.hasStrictFDerivAt' hd hn
  have h0 : chart (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := chart_zero
  refine ⟨hc.localInverse hd hn, ?_, ?_, ?_, ?_⟩
  · have h := hc.to_localInverse hd hn
    rwa [h0] at h
  · have h := hc.localInverse_apply_image hd hn
    rwa [h0] at h
  · have h := hs.localInverse_tendsto
    rw [h0] at h
    exact h
  · have h := hs.eventually_right_inverse
    rw [h0] at h
    exact h

/-- Near `0` the upper triangular factor `1 + P_b X` has nonzero diagonal entries. -/
theorem eventually_diag_ne_zero :
    ∀ᶠ X in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ∀ j, (1 + upperPart X) j j ≠ 0 := by
  rw [Filter.eventually_all]
  intro j
  have hc : Continuous fun X : Matrix (Fin n) (Fin n) ℂ => (1 + upperPart X) j j :=
    ((LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ j j)).continuous.comp
      (continuous_const.add (LinearMap.toContinuousLinearMap upperPart).continuous))
  have h1 : (1 + upperPart (0 : Matrix (Fin n) (Fin n) ℂ)) j j ≠ 0 := by simp
  exact hc.continuousAt.eventually_ne h1

end Chart

end Langlands.Archimedean
