import Langlands.Representation.Archimedean.KIntegralInvariance
import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Matrix coefficients of real principal series against the dual principal series

For functions `w, ψ` on `GL_n(ℝ)` put `mc w ψ g = ∫_{O(n)} w(k g) ψ(k) dk` (normalized Haar
measure `haarK n`). For `w` in the real standard module of `ds` and `ψ` in the real standard
module of `ds'`, with pointwise inverse position characters, this is the invariant pairing of
the right translate `R(g) w` with `ψ`. This file proves the three properties used in
Casselman's matrix-coefficient argument:

* `mc_eq_zero_of_orthogonal`: if `ψ` is orthogonal on `O(n)` to a `(𝔤, K)`-stable space `W`
  of `O(n)`-finite functions, then `mc w ψ g = 0` for all `w ∈ W` and all `g`;
* `mc_rightDerivative`: `mc (R(Y) w) ψ g = - mc w (R(g Y g⁻¹) ψ) g`;
* `hasDerivAt_mc`: along a diagonal one-parameter subgroup, `t ↦ mc w ψ (g exp(tH))` has
  derivative `mc (R(H) w) ψ (g exp(tH))`.

The first and third are the Library's `principalSeriesOrthogonalityInvariance` and
`MatrixCoefficientAnalytic.analyticAt_matrixCoefficient`, transported from the measure on
`Matrix.unitaryGroup` to `haarK n`; the second combines `KIntegralInvariance.rightDerivative_mul_eq`
with `RealPrincipalSeriesDuality.integral_rightDerivative_eq_zero`.
-/

noncomputable section

open MeasureTheory

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

-- The charts on units need reduction through the normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

namespace RealJacquetCoefficient

open RealPrincipalSeriesDuality Langlands.LocalFactor.Archimedean

attribute [local instance] measurableSpaceK

local instance borelSpaceK₃ (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {n : ℕ}

/-! ## From `O(n) ⊆ GL_n(ℝ)` to unitary matrices -/

section Bridge

/-- An element of `O(n) ⊆ GL_n(ℝ)` as a unitary matrix. -/
def toUG (k : unitaryCompact ℝ n) : Matrix.unitaryGroup (Fin n) ℝ :=
  ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩

theorem toUnits_toUG (k : unitaryCompact ℝ n) :
    Unitary.toUnits (toUG k) = (k : Langlands.GeneralLinear n ℝ) :=
  Units.ext rfl

theorem continuous_toUG : Continuous (toUG (n := n)) :=
  continuous_unitaryCompact_val.subtype_mk _

theorem continuous_toUnits :
    Continuous (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℝ → Langlands.GeneralLinear n ℝ) :=
  Units.continuous_iff.mpr ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩

variable (n) in
/-- The Haar measure of `O(n)`, transported to the unitary matrices. -/
def μK : Measure (Matrix.unitaryGroup (Fin n) ℝ) := (haarK n).map toUG

instance : IsFiniteMeasure (μK n) := by
  unfold μK
  infer_instance

theorem integral_μK {F : Matrix.unitaryGroup (Fin n) ℝ → ℂ} (hF : Continuous F) :
    ∫ κ, F κ ∂μK n = ∫ k, F (toUG k) ∂haarK n :=
  integral_map continuous_toUG.measurable.aemeasurable hF.aestronglyMeasurable

end Bridge

/-! ## Matrix coefficients -/

section Coefficient

/-- The matrix coefficient `g ↦ ∫_{O(n)} w(k g) ψ(k) dk`. -/
def mc (w ψ : Langlands.GeneralLinear n ℝ → ℂ) (g : Langlands.GeneralLinear n ℝ) : ℂ :=
  ∫ k, w ((k : Langlands.GeneralLinear n ℝ) * g) * ψ (k : Langlands.GeneralLinear n ℝ) ∂haarK n

theorem mc_eq_matrixCoefficient {w ψ : Langlands.GeneralLinear n ℝ → ℂ} (hw : Continuous w)
    (hψ : Continuous ψ) (g : Langlands.GeneralLinear n ℝ) :
    mc w ψ g = MatrixCoefficientAnalytic.matrixCoefficient (μK n) w
      (fun κ => ψ (Unitary.toUnits κ)) g := by
  rw [MatrixCoefficientAnalytic.matrixCoefficient, integral_μK]
  · simp only [toUnits_toUG]
    rfl
  · exact (hw.comp (continuous_toUnits.mul continuous_const)).mul (hψ.comp continuous_toUnits)

theorem continuous_mc_integrand {w ψ : Langlands.GeneralLinear n ℝ → ℂ} (hw : Continuous w)
    (hψ : Continuous ψ) (g : Langlands.GeneralLinear n ℝ) :
    Continuous fun k : unitaryCompact ℝ n =>
      w ((k : Langlands.GeneralLinear n ℝ) * g) * ψ (k : Langlands.GeneralLinear n ℝ) :=
  (hw.comp (continuous_subtype_val.mul continuous_const)).mul (hψ.comp continuous_subtype_val)

theorem mc_add_left {w₁ w₂ ψ : Langlands.GeneralLinear n ℝ → ℂ} (hw₁ : Continuous w₁)
    (hw₂ : Continuous w₂) (hψ : Continuous ψ) (g : Langlands.GeneralLinear n ℝ) :
    mc (w₁ + w₂) ψ g = mc w₁ ψ g + mc w₂ ψ g := by
  unfold mc
  rw [← integral_add (integrable_of_continuous (continuous_mc_integrand hw₁ hψ g))
    (integrable_of_continuous (continuous_mc_integrand hw₂ hψ g))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [Pi.add_apply, add_mul]

theorem mc_smul_left (c : ℂ) (w ψ : Langlands.GeneralLinear n ℝ → ℂ)
    (g : Langlands.GeneralLinear n ℝ) : mc (c • w) ψ g = c * mc w ψ g := by
  unfold mc
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem mc_add_right {w ψ₁ ψ₂ : Langlands.GeneralLinear n ℝ → ℂ} (hw : Continuous w)
    (hψ₁ : Continuous ψ₁) (hψ₂ : Continuous ψ₂) (g : Langlands.GeneralLinear n ℝ) :
    mc w (ψ₁ + ψ₂) g = mc w ψ₁ g + mc w ψ₂ g := by
  unfold mc
  rw [← integral_add (integrable_of_continuous (continuous_mc_integrand hw hψ₁ g))
    (integrable_of_continuous (continuous_mc_integrand hw hψ₂ g))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [Pi.add_apply, mul_add]

theorem mc_smul_right (c : ℂ) (w ψ : Langlands.GeneralLinear n ℝ → ℂ)
    (g : Langlands.GeneralLinear n ℝ) : mc w (c • ψ) g = c * mc w ψ g := by
  unfold mc
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem mc_sub_left {w₁ w₂ ψ : Langlands.GeneralLinear n ℝ → ℂ} (hw₁ : Continuous w₁)
    (hw₂ : Continuous w₂) (hψ : Continuous ψ) (g : Langlands.GeneralLinear n ℝ) :
    mc (w₁ - w₂) ψ g = mc w₁ ψ g - mc w₂ ψ g := by
  have h := mc_add_left hw₂ (hw₁.sub hw₂) hψ g
  rw [add_sub_cancel] at h
  rw [h, add_sub_cancel_left]

/-- Right translation by `O(n)` moves from `ψ` to `w` at `g = 1`. -/
theorem mc_one_rightTranslation (w ψ : Langlands.GeneralLinear n ℝ → ℂ)
    (k : unitaryCompact ℝ n) :
    mc w (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) ψ) 1 =
      mc (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        ((k : Langlands.GeneralLinear n ℝ)⁻¹) w) ψ 1 := by
  unfold mc
  conv_rhs => rw [← integral_mul_right_eq_self _ k]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change w ((x : Langlands.GeneralLinear n ℝ) * 1) * ψ ((x : Langlands.GeneralLinear n ℝ) * k) =
    w (((x * k : unitaryCompact ℝ n) : Langlands.GeneralLinear n ℝ) * 1 *
      (k : Langlands.GeneralLinear n ℝ)⁻¹) * ψ ((x * k : unitaryCompact ℝ n) : Langlands.GeneralLinear n ℝ)
  simp only [Subgroup.coe_mul, mul_one, mul_inv_cancel_right]

theorem kFinite_le_principalSeries {ds : List RealBlock} {w : Langlands.GeneralLinear n ℝ → ℂ}
    (hw : w ∈ kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    w ∈ kFiniteFunctions (principalSeries ℝ n (realPositionCharacter ds)) (unitaryCompact ℝ n) :=
  ⟨realStandardModule_le_principalSeries n ds hw.1, hw.2⟩

/-- **Orthogonality.** If `ψ` is orthogonal on `O(n)` to a space `W` of `O(n)`-finite functions
of a real standard module that is stable under right translation by `O(n)` and under right
derivatives, then every matrix coefficient `mc w ψ` with `w ∈ W` vanishes. -/
theorem mc_eq_zero_of_orthogonal {ds : List RealBlock}
    {W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)}
    (hW : W ≤ kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (hWK : ∀ k ∈ unitaryCompact ℝ n, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k w ∈ W)
    (hWD : ∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ w ∈ W, rightDerivative (matrixModel ℝ n) X w ∈ W)
    {ψ : Langlands.GeneralLinear n ℝ → ℂ} (hψ : Continuous ψ)
    (h1 : ∀ w ∈ W, mc w ψ 1 = 0) : ∀ w ∈ W, ∀ g, mc w ψ g = 0 := by
  have hcont : ∀ w ∈ W, Continuous w := fun w hw =>
    (contMDiff_of_mem_realStandardModule (hW hw).1).continuous
  intro w hw g
  have h := principalSeriesOrthogonalityInvariance n ds W (fun f hf => kFinite_le_principalSeries
    (hW hf)) hWK hWD (μK n) inferInstance (fun κ => ψ (Unitary.toUnits κ))
    (hψ.comp continuous_toUnits) (fun w' hw' => ?_) w hw g
  · have := mc_eq_matrixCoefficient (hcont w hw) hψ g
    rw [this]
    exact h
  · have := mc_eq_matrixCoefficient (hcont w' hw') hψ 1
    rw [h1 w' hw', MatrixCoefficientAnalytic.matrixCoefficient] at this
    simpa only [mul_one] using this.symm

/-- **Adjoint.** For `w` and `ψ` in real standard modules with pointwise inverse position
characters, `mc (R(Y) w) ψ g = - mc w (R(g Y g⁻¹) ψ) g`. -/
theorem mc_rightDerivative {ds ds' : List RealBlock}
    (hχ : ∀ (i : ℕ) (x : ℝˣ), realPositionCharacter ds i x * realPositionCharacter ds' i x = 1)
    {w ψ : Langlands.GeneralLinear n ℝ → ℂ} (hw : w ∈ realStandardModule n ds)
    (hψ : ψ ∈ realStandardModule n ds') (Y : Matrix (Fin n) (Fin n) ℝ)
    (g : Langlands.GeneralLinear n ℝ) :
    mc (rightDerivative (matrixModel ℝ n) Y w) ψ g =
      -mc w (rightDerivative (matrixModel ℝ n) ((g : Matrix (Fin n) (Fin n) ℝ) * Y *
        ((g⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) ψ) g := by
  set Z : Matrix (Fin n) (Fin n) ℝ := (g : Matrix (Fin n) (Fin n) ℝ) * Y *
    ((g⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)
  set f : Langlands.GeneralLinear n ℝ → ℂ := fun x => w (x * g) with hfdef
  have hf : f ∈ realStandardModule n ds := rightTranslation_mem_realStandardModule_of_mem hw g
  have hfs := contMDiff_of_mem_realStandardModule hf
  have hψs := contMDiff_of_mem_realStandardModule hψ
  have hZf := (contMDiff_of_mem_realStandardModule
    (rightDerivative_mem_realStandardModule_of_mem hf Z)).continuous
  have hZψ := (contMDiff_of_mem_realStandardModule
    (rightDerivative_mem_realStandardModule_of_mem hψ Z)).continuous
  have h0 := integral_rightDerivative_eq_zero (contMDiff_mul_fun hfs hψs)
    (isModulusEquivariant_mul hχ (realStandardModule_le_principalSeries n ds hf)
      (realStandardModule_le_principalSeries n ds' hψ)) Z
  simp_rw [rightDerivative_mul_fun hfs hψs Z] at h0
  rw [integral_add (integrable_mul_of_continuous hZf hψs.continuous)
    (integrable_mul_of_continuous hfs.continuous hZψ)] at h0
  have e1 : mc (rightDerivative (matrixModel ℝ n) Y w) ψ g =
      ∫ k, rightDerivative (matrixModel ℝ n) Z f (k : Langlands.GeneralLinear n ℝ) *
        ψ (k : Langlands.GeneralLinear n ℝ) ∂haarK n := by
    unfold mc
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    rw [KIntegralInvariance.rightDerivative_mul_eq (contMDiff_of_mem_realStandardModule hw) g]
  rw [e1, eq_neg_iff_add_eq_zero]
  exact h0

/-- **Ray derivative.** For an `O(n)`-finite function `w` of a real standard module and a
continuous `ψ`, the matrix coefficient along `t ↦ g exp(tH)`, `H = diag(h)`, has derivative
`mc (R(H) w) ψ (g exp(tH))`. -/
theorem hasDerivAt_mc {ds : List RealBlock} {w : Langlands.GeneralLinear n ℝ → ℂ}
    (hw : w ∈ kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    {ψ : Langlands.GeneralLinear n ℝ → ℂ} (hψ : Continuous ψ) (g : Langlands.GeneralLinear n ℝ)
    (h : Fin n → ℝ) (t₀ : ℝ) :
    HasDerivAt (fun t => mc w ψ (g * MatrixCoefficientAnalytic.expDiagonal h t))
      (mc (rightDerivative (matrixModel ℝ n) (Matrix.diagonal h) w) ψ
        (g * MatrixCoefficientAnalytic.expDiagonal h t₀)) t₀ := by
  have hwc := (contMDiff_of_mem_realStandardModule hw.1).continuous
  have hDwc := (contMDiff_of_mem_realStandardModule
    (rightDerivative_mem_realStandardModule_of_mem hw.1 (Matrix.diagonal h))).continuous
  have key := (MatrixCoefficientAnalytic.analyticAt_matrixCoefficient (μK n)
    (GramFormula.realPositionExponent ds) (GramFormula.realPositionCharacter_eq_signUnit_mul ds)
    (kFinite_le_principalSeries hw) (hψ.comp continuous_toUnits) g h t₀).2
  rw [mc_eq_matrixCoefficient hDwc hψ]
  have hfun : (fun t => mc w ψ (g * MatrixCoefficientAnalytic.expDiagonal h t)) =
      fun t => MatrixCoefficientAnalytic.matrixCoefficient (μK n) w
        (fun κ => ψ (Unitary.toUnits κ)) (g * MatrixCoefficientAnalytic.expDiagonal h t) :=
    funext fun t => mc_eq_matrixCoefficient hwc hψ _
  rw [hfun]
  exact key

end Coefficient

/-! ## Growth along a diagonal ray -/

section Growth

open GramFormula Langlands.GeneralLinear

theorem sq_le_trace_mul_transpose (M : Matrix (Fin n) (Fin n) ℝ) (l : Fin n) :
    M l l ^ 2 ≤ (M * M.transpose).trace := by
  have h1 : M l l ^ 2 ≤ ∑ q, M l q * M l q := by
    rw [sq]
    exact Finset.single_le_sum (f := fun q => M l q * M l q) (fun q _ => mul_self_nonneg _)
      (Finset.mem_univ l)
  have h2 : ∑ q, M l q * M l q ≤ ∑ p, ∑ q, M p q * M p q :=
    Finset.single_le_sum (f := fun p => ∑ q, M p q * M p q)
      (fun p _ => Finset.sum_nonneg fun q _ => mul_self_nonneg _) (Finset.mem_univ l)
  calc M l l ^ 2 ≤ _ := h1.trans h2
    _ = (M * M.transpose).trace := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]

theorem trace_mul_orth (M k : Matrix (Fin n) (Fin n) ℝ) (hk : k * k.transpose = 1) :
    ((M * k) * (M * k).transpose).trace = (M * M.transpose).trace := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc k, hk, Matrix.one_mul]

theorem trace_orth_mul (k M : Matrix (Fin n) (Fin n) ℝ) (hk : k.transpose * k = 1) :
    ((k * M) * (k * M).transpose).trace = (M * M.transpose).trace := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, hk, Matrix.mul_one]

theorem abs_det_eq_one_of_mem {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    |(k : Matrix (Fin n) (Fin n) ℝ).det| = 1 := by
  have h := congrArg Matrix.det (mul_transpose_eq_one_of_mem hk)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← sq, ← sq_abs] at h
  exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).mp h

/-- The diagonal entries of the Iwasawa decomposition `x = d u k` are bounded by the
Frobenius norm of `x`. -/
theorem sq_le_trace_of_iwasawa (d : Fin n → ℝˣ) (u : upperUnipotent n ℝ)
    {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) (l : Fin n) :
    ((d l : ℝ)) ^ 2 ≤ ((((Iwasawa.diagonalUnits d : Langlands.GeneralLinear n ℝ) *
        (u : Langlands.GeneralLinear n ℝ) * k : Langlands.GeneralLinear n ℝ) :
          Matrix (Fin n) (Fin n) ℝ) *
        (((Iwasawa.diagonalUnits d : Langlands.GeneralLinear n ℝ) *
        (u : Langlands.GeneralLinear n ℝ) * k : Langlands.GeneralLinear n ℝ) :
          Matrix (Fin n) (Fin n) ℝ).transpose).trace := by
  have e : (((Iwasawa.diagonalUnits d : Langlands.GeneralLinear n ℝ) *
      (u : Langlands.GeneralLinear n ℝ) * k : Langlands.GeneralLinear n ℝ) :
        Matrix (Fin n) (Fin n) ℝ) = (Matrix.diagonal (fun l => (d l : ℝ)) *
          ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) *
            (k : Matrix (Fin n) (Fin n) ℝ) := rfl
  rw [e, trace_mul_orth _ _ (mul_transpose_eq_one_of_mem hk), ← diagonal_mul_apply_self d u l]
  exact sq_le_trace_mul_transpose _ l

/-- The product of the diagonal entries of the Iwasawa decomposition `x = d u k` is `|det x|`
up to sign. -/
theorem abs_prod_eq_abs_det_of_iwasawa (d : Fin n → ℝˣ) (u : upperUnipotent n ℝ)
    {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    ∏ l, |(d l : ℝ)| = |(((Iwasawa.diagonalUnits d : Langlands.GeneralLinear n ℝ) *
        (u : Langlands.GeneralLinear n ℝ) * k : Langlands.GeneralLinear n ℝ) :
          Matrix (Fin n) (Fin n) ℝ).det| := by
  have e : (((Iwasawa.diagonalUnits d : Langlands.GeneralLinear n ℝ) *
      (u : Langlands.GeneralLinear n ℝ) * k : Langlands.GeneralLinear n ℝ) :
        Matrix (Fin n) (Fin n) ℝ) = (Matrix.diagonal (fun l => (d l : ℝ)) *
          ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) *
            (k : Matrix (Fin n) (Fin n) ℝ) := rfl
  have hU : ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular u.property.1]
    simp
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, hU, mul_one, abs_mul,
    abs_det_eq_one_of_mem hk, mul_one, Finset.abs_prod]

theorem trace_unitary_mul_expDiagonal {κ : Langlands.GeneralLinear n ℝ}
    (hκ : κ ∈ unitaryCompact ℝ n) (h : Fin n → ℝ) (s : ℝ) :
    (((κ * MatrixCoefficientAnalytic.expDiagonal h s : Langlands.GeneralLinear n ℝ) :
        Matrix (Fin n) (Fin n) ℝ) *
      ((κ * MatrixCoefficientAnalytic.expDiagonal h s : Langlands.GeneralLinear n ℝ) :
        Matrix (Fin n) (Fin n) ℝ).transpose).trace = ∑ j, Real.exp (s * h j) ^ 2 := by
  have hκκ : (κ : Matrix (Fin n) (Fin n) ℝ).transpose * κ = 1 :=
    mul_eq_one_comm.mp (mul_transpose_eq_one_of_mem hκ)
  rw [Units.val_mul, trace_orth_mul _ _ hκκ, MatrixCoefficientAnalytic.expDiagonal_val,
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp only [sq]

theorem abs_det_unitary_mul_expDiagonal {κ : Langlands.GeneralLinear n ℝ}
    (hκ : κ ∈ unitaryCompact ℝ n) (h : Fin n → ℝ) (s : ℝ) :
    |((κ * MatrixCoefficientAnalytic.expDiagonal h s : Langlands.GeneralLinear n ℝ) :
        Matrix (Fin n) (Fin n) ℝ).det| = Real.exp (s * ∑ j, h j) := by
  rw [Units.val_mul, Matrix.det_mul, MatrixCoefficientAnalytic.expDiagonal_val,
    Matrix.det_diagonal, abs_mul, abs_det_eq_one_of_mem hκ, one_mul, Finset.mul_sum,
    Real.exp_sum, Finset.abs_prod]
  exact Finset.prod_congr rfl fun j _ => abs_of_pos (Real.exp_pos _)

/-- An elementary bound: positive numbers `y_l` with `y_l² ≤ ∑_j e^{2 s h_j}` and
`∏_l y_l = e^{s ∑_j h_j}` satisfy `|log y_l| ≤ n (log n + 2 s ∑_j |h_j|)`. -/
theorem abs_log_le_of_bounds {y : Fin n → ℝ} (hy : ∀ l, 0 < y l) {h : Fin n → ℝ} {s : ℝ}
    (hs : 0 ≤ s) (hT : ∀ l, y l ^ 2 ≤ ∑ j, Real.exp (s * h j) ^ 2)
    (hP : ∏ l, y l = Real.exp (s * ∑ j, h j)) (l : Fin n) :
    |Real.log (y l)| ≤ n * (Real.log n + 2 * s * ∑ j, |h j|) := by
  set L := ∑ j, |h j| with hLdef
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fin.pos l).ne'
  have hL : 0 ≤ L := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn
  have hhL : ∀ j, h j ≤ L := fun j =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |h j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ j))
  have hsum : ∑ j, Real.exp (s * h j) ^ 2 ≤ n * Real.exp (2 * s * L) := by
    calc ∑ j, Real.exp (s * h j) ^ 2 ≤ ∑ _j : Fin n, Real.exp (2 * s * L) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← Real.exp_nat_mul]
          apply Real.exp_le_exp.mpr
          have := mul_le_mul_of_nonneg_left (hhL j) hs
          push_cast
          linarith
      _ = n * Real.exp (2 * s * L) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  set B := (Real.log n + 2 * s * L) / 2 with hBdef
  have hB : ∀ m, Real.log (y m) ≤ B := by
    intro m
    have h1 : Real.log (y m ^ 2) ≤ Real.log (n * Real.exp (2 * s * L)) :=
      Real.log_le_log (pow_pos (hy m) 2) ((hT m).trans hsum)
    rw [Real.log_pow, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at h1
    push_cast at h1
    rw [hBdef]
    linarith
  have hsumlog : ∑ m, Real.log (y m) = s * ∑ j, h j := by
    rw [← Real.log_prod (fun m _ => (hy m).ne'), hP, Real.log_exp]
  have hlow : -(s * L) ≤ s * ∑ j, h j := by
    have h1 : -L ≤ ∑ j, h j := by
      have := Finset.abs_sum_le_sum_abs h Finset.univ
      linarith [neg_abs_le (∑ j, h j)]
    nlinarith
  have herase : ∑ m ∈ Finset.univ.erase l, Real.log (y m) ≤ ((n : ℝ) - 1) * B := by
    calc ∑ m ∈ Finset.univ.erase l, Real.log (y m) ≤ ∑ _m ∈ Finset.univ.erase l, B :=
          Finset.sum_le_sum fun m _ => hB m
      _ = ((n : ℝ) - 1) * B := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (Nat.succ_le_of_lt (Fin.pos l)), Nat.cast_one]
  have hsplit := Finset.add_sum_erase Finset.univ (fun m => Real.log (y m)) (Finset.mem_univ l)
  have hB0 : s * L ≤ B := by rw [hBdef]; linarith
  have hBnn : 0 ≤ B := le_trans (mul_nonneg hs hL) hB0
  have h2B : n * (Real.log n + 2 * s * L) = 2 * n * B := by rw [hBdef]; ring
  rw [h2B, abs_le]
  constructor
  · nlinarith [hB l, mul_nonneg (sub_nonneg.mpr hn) hBnn]
  · nlinarith [hB l, mul_nonneg (sub_nonneg.mpr hn) hBnn]

/-- The principal series character is bounded by the absolute values of the logarithms of the
diagonal entries. -/
theorem norm_principalSeriesCharacter_le (ds : List RealBlock) (d : Fin n → ℝˣ) :
    ‖principalSeriesCharacter ℝ n (realPositionCharacter ds) d‖ ≤
      (∏ l : Fin n, (‖realPositionCharacter ds l 1‖ + ‖realPositionCharacter ds l (-1)‖)) *
        Real.exp (∑ l : Fin n, |(shiftedExponent n (realPositionExponent ds) l).re| *
          |Real.log (abs (d l : ℝ))|) := by
  rw [principalSeriesCharacter_eq (realPositionExponent ds)
    (realPositionCharacter_eq_signUnit_mul ds) d, norm_mul, mul_comm]
  refine mul_le_mul ?_ ?_ (norm_nonneg _)
    (Finset.prod_nonneg fun l _ => add_nonneg (norm_nonneg _) (norm_nonneg _))
  · simp only [principalSeriesCharacter]
    rw [norm_prod]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun l _ => ?_
    have hs1 : ‖(((signUnit (d l) : ℝˣ) : ℝ))‖ = 1 := by
      rw [signUnit_val, Real.norm_eq_abs, abs_signReal]
    rw [norm_mul, Module.finrank_self, pow_one, hs1, Complex.ofReal_one, Complex.one_cpow,
      norm_one, mul_one]
    unfold signUnit
    split_ifs
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  · rw [norm_prod, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun l _ => ?_
    have hpos : 0 < |(d l : ℝ)| := abs_pos.mpr (d l).ne_zero
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, Real.rpow_def_of_pos hpos]
    apply Real.exp_le_exp.mpr
    calc Real.log |(d l : ℝ)| * (shiftedExponent n (realPositionExponent ds) l).re
        ≤ |Real.log |(d l : ℝ)| * (shiftedExponent n (realPositionExponent ds) l).re| :=
          le_abs_self _
      _ = _ := by rw [abs_mul, mul_comm]

/-- **Growth.** Along the diagonal ray `s ↦ exp(s H)`, `s ≥ 0`, the matrix coefficients of the
functions of a real standard module grow at most exponentially, with an exponent `c` that
depends only on the standard module and `H`. -/
theorem exists_growth (ds : List RealBlock) (h : Fin n → ℝ) :
    ∃ c : ℝ, ∀ w ∈ realStandardModule n ds, ∀ ψ : Langlands.GeneralLinear n ℝ → ℂ,
      Continuous ψ → ∃ C : ℝ, ∀ s : ℝ, 0 ≤ s →
        ‖mc w ψ (MatrixCoefficientAnalytic.expDiagonal h s)‖ ≤ C * Real.exp (c * s) := by
  set σ : ℝ := ∑ l : Fin n, |(shiftedExponent n (realPositionExponent ds) l).re| with hσ
  set L : ℝ := ∑ j, |h j| with hL
  set Ms : ℝ := ∏ l : Fin n,
    (‖realPositionCharacter ds l 1‖ + ‖realPositionCharacter ds l (-1)‖) with hMs
  have hMs0 : 0 ≤ Ms := Finset.prod_nonneg fun l _ => add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hσ0 : 0 ≤ σ := Finset.sum_nonneg fun l _ => abs_nonneg _
  refine ⟨σ * (2 * n * L), fun w hw ψ hψ => ?_⟩
  have hwc := (contMDiff_of_mem_realStandardModule hw).continuous
  obtain ⟨Mw, hMw⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_comp_val (n := n) hwc).continuousOn
  obtain ⟨Mψ, hMψ⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_comp_val (n := n) hψ).continuousOn
  have hMw0 : 0 ≤ Mw := (norm_nonneg _).trans (hMw 1 (Set.mem_univ _))
  refine ⟨Ms * Real.exp (σ * (n * Real.log n)) * Mw * Mψ, fun s hs => ?_⟩
  have hpt : ∀ κ : unitaryCompact ℝ n,
      ‖w ((κ : Langlands.GeneralLinear n ℝ) * MatrixCoefficientAnalytic.expDiagonal h s) *
        ψ (κ : Langlands.GeneralLinear n ℝ)‖ ≤
      Ms * Real.exp (σ * (n * Real.log n)) * Mw * Mψ * Real.exp (σ * (2 * n * L) * s) := by
    intro κ
    obtain ⟨d, u, k', hk', hx⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact
      ((κ : Langlands.GeneralLinear n ℝ) * MatrixCoefficientAnalytic.expDiagonal h s)
    have hlog : ∀ l, |Real.log (abs (d l : ℝ))| ≤ n * (Real.log n + 2 * s * L) := by
      refine abs_log_le_of_bounds (fun l => abs_pos.mpr (d l).ne_zero) hs (fun l => ?_) ?_
      · rw [sq_abs, ← trace_unitary_mul_expDiagonal κ.2 h s, hx]
        exact sq_le_trace_of_iwasawa d u hk' l
      · rw [abs_prod_eq_abs_det_of_iwasawa d u hk', ← hx, abs_det_unitary_mul_expDiagonal κ.2]
    have hps := ((mem_principalSeries_iff ℝ n _ w).mp
      (realStandardModule_le_principalSeries n ds hw)).2 d u k'
    have hchar := norm_principalSeriesCharacter_le ds d
    have hexp : Real.exp (∑ l : Fin n, |(shiftedExponent n (realPositionExponent ds) l).re| *
        |Real.log (abs (d l : ℝ))|) ≤
          Real.exp (σ * (n * Real.log n)) * Real.exp (σ * (2 * n * L) * s) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      calc ∑ l : Fin n, |(shiftedExponent n (realPositionExponent ds) l).re| *
            |Real.log (abs (d l : ℝ))|
          ≤ ∑ l : Fin n, |(shiftedExponent n (realPositionExponent ds) l).re| *
            (n * (Real.log n + 2 * s * L)) :=
            Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hlog l) (abs_nonneg _)
        _ = σ * (n * Real.log n) + σ * (2 * n * L) * s := by rw [← Finset.sum_mul]; ring
    rw [hx, hps, norm_mul, norm_mul]
    have h1 := hMw ⟨k', hk'⟩ (Set.mem_univ _)
    have h2 := hMψ κ (Set.mem_univ _)
    simp only at h1 h2
    calc ‖principalSeriesCharacter ℝ n (realPositionCharacter ds) d‖ * ‖w k'‖ *
          ‖ψ (κ : Langlands.GeneralLinear n ℝ)‖
        ≤ (Ms * (Real.exp (σ * (n * Real.log n)) * Real.exp (σ * (2 * n * L) * s))) * Mw *
            Mψ := by
          gcongr
          · exact hchar.trans (mul_le_mul_of_nonneg_left hexp hMs0)
      _ = _ := by ring
  calc ‖mc w ψ (MatrixCoefficientAnalytic.expDiagonal h s)‖
      ≤ (Ms * Real.exp (σ * (n * Real.log n)) * Mw * Mψ * Real.exp (σ * (2 * n * L) * s)) *
          (haarK n).real Set.univ :=
        norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hpt)
    _ = _ := by rw [probReal_univ, mul_one]

end Growth

end RealJacquetCoefficient

end Langlands.Archimedean
