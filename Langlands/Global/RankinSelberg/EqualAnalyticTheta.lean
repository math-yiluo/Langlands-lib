import Langlands.Global.RankinSelberg.EqualAnalyticPoissonGL
import Langlands.Global.RankinSelberg.UnequalAnalyticPoints
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! # The theta series of a row function

For `Φ : 𝔸^n → ℂ` and `M ∈ GL_n(𝔸)` let `Θ(Φ, M) = Σ_(ξ ∈ F^n, ξ ≠ 0) Φ(ξ M)` (`thetaSum`), and
`Θ⁺(Φ, M) = Σ_(ξ ≠ 0) |Φ(ξ M)|` in `[0, ∞]` (`thetaNorm`).

* Both are invariant under `M ↦ γ M`, `γ ∈ GL_n(F)`.
* **Poisson summation** (`thetaSum_poisson`): for `Φ ∈ S(𝔸^n)`,
  `Θ(Φ, M) + Φ(0) = |det M|⁻¹ (Θ(Φ̂, ᵗM⁻¹) + Φ̂(0))`.
* **Bound in torus coordinates** (`exists_thetaNorm_le`): for a dominated `Φ`, a compact set `Q`
  and `N > n [F:ℚ]`, `Θ⁺(Φ, A(x) q) ≤ K exp (-N t)` whenever `t ≤ x_j` for all `j` and `q ∈ Q`;
  here `A(x)` is the archimedean torus element `diag(e^(x_1), …, e^(x_n))`.
-/

noncomputable section
universe u
open NumberField MeasureTheory Set Filter Topology
open scoped Classical Matrix ENNReal

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

open Langlands.Global Langlands.Automorphic.CuspidalWhittaker

variable (F : Type u) [Field F] [NumberField F]

/-- The theta series `Θ(Φ, M) = Σ_(ξ ∈ F^n, ξ ≠ 0) Φ(ξ M)` (an unconditional sum). -/
def thetaSum (n : ℕ) (Φ : RowVector F n → ℂ) (M : AdelicGL F n) : ℂ :=
  ∑' C : RatRow F n, if C = 0 then 0 else Φ (ratRow F n C * (M : Matrix (Fin n) (Fin n) (Adeles F)))

/-- The majorant `Θ⁺(Φ, M) = Σ_(ξ ≠ 0) ‖Φ(ξ M)‖` in `[0, ∞]`. -/
def thetaNorm (n : ℕ) (Φ : RowVector F n → ℂ) (M : AdelicGL F n) : ℝ≥0∞ :=
  ∑' C : RatRow F n,
    if C = 0 then 0 else ‖Φ (ratRow F n C * (M : Matrix (Fin n) (Fin n) (Adeles F)))‖ₑ

instance ratRow_countable (n : ℕ) : Countable (RatRow F n) := by
  have := numberField_countable F
  exact inferInstanceAs (Countable (Fin 1 → Fin n → F))

variable {F}

theorem enorm_thetaSum_le (n : ℕ) (Φ : RowVector F n → ℂ) (M : AdelicGL F n) :
    ‖thetaSum F n Φ M‖ₑ ≤ thetaNorm F n Φ M := by
  refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun C => ?_)
  split_ifs <;> simp

variable (F)

theorem summable_rowMul (n : ℕ) {Φ : RowVector F n → ℂ} (hΦ : IsRowDominated F n Φ)
    (M : AdelicGL F n) :
    Summable fun C : RatRow F n => Φ (ratRow F n C * (M : Matrix (Fin n) (Fin n) (Adeles F))) := by
  have h := summable_periodization F n (IsRowDominated.comp_mul F n hΦ M) 0
  simpa only [add_zero] using h

theorem thetaSum_add (n : ℕ) {Φ : RowVector F n → ℂ} (hΦ : IsRowDominated F n Φ)
    (M : AdelicGL F n) :
    thetaSum F n Φ M + Φ 0 =
      ∑' C : RatRow F n, Φ (ratRow F n C * (M : Matrix (Fin n) (Fin n) (Adeles F))) := by
  rw [(summable_rowMul F n hΦ M).tsum_eq_add_tsum_ite 0, ratRow_zero, Matrix.zero_mul, add_comm]
  rfl

/-- **Poisson summation for the theta series.** -/
theorem thetaSum_poisson [CompactSpace (AdeleQuotient F)] (n : ℕ) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) {Φ : RowVector F n → ℂ}
    (hΦ : Φ ∈ schwartzBruhat F n) (M : AdelicGL F n) :
    thetaSum F n Φ M + Φ 0 = ((absDet F n M)⁻¹ : ℂ) *
      (thetaSum F n (fourierTransform F n ψ Φ) (GeneralLinear.inverseTranspose n (Adeles F) M) +
        fourierTransform F n ψ Φ 0) := by
  rw [thetaSum_add F n (schwartzBruhat_properties F n hΦ).2.2 M,
    ← (hasSum_poisson_mul F n ψ hψ hΦ M).tsum_eq, tsum_mul_left,
    thetaSum_add F n (fourierTransform_properties F n ψ hψ hΦ).2]

/-! ### Invariance under rational points -/

/-- Right multiplication of rational rows by a rational matrix. -/
def ratRowMulEquiv (n : ℕ) (c : RationalGL F n) : RatRow F n ≃ RatRow F n where
  toFun C := C * (c : Matrix (Fin n) (Fin n) F)
  invFun C := C * ((c⁻¹ : RationalGL F n) : Matrix (Fin n) (Fin n) F)
  left_inv C := by
    simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  right_inv C := by
    simp only [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

omit [NumberField F] in
theorem ratRowMulEquiv_zero (n : ℕ) (c : RationalGL F n) : ratRowMulEquiv F n c 0 = 0 := by
  show (0 : Matrix (Fin 1) (Fin n) F) * (c : Matrix (Fin n) (Fin n) F) = 0
  exact Matrix.zero_mul _

omit [NumberField F] in
theorem ratRowMulEquiv_eq_zero_iff (n : ℕ) (c : RationalGL F n) (C : RatRow F n) :
    ratRowMulEquiv F n c C = 0 ↔ C = 0 := by
  have h := (ratRowMulEquiv F n c).injective.eq_iff (a := C) (b := 0)
  rwa [ratRowMulEquiv_zero F n c] at h

theorem ratRow_mul_rational (n : ℕ) (C : RatRow F n) (c : RationalGL F n) (M : AdelicGL F n) :
    ratRow F n C * ((AdelicGL.rational F n c * M : AdelicGL F n) :
        Matrix (Fin n) (Fin n) (Adeles F)) =
      ratRow F n (ratRowMulEquiv F n c C) * (M : Matrix (Fin n) (Fin n) (Adeles F)) := by
  rw [Units.val_mul, ← Matrix.mul_assoc]
  congr 1
  show C.map (algebraMap F (Adeles F)) * (c : Matrix (Fin n) (Fin n) F).map
    (algebraMap F (Adeles F)) = (C * (c : Matrix (Fin n) (Fin n) F)).map (algebraMap F (Adeles F))
  rw [Matrix.map_mul]

theorem thetaSum_rational_mul (n : ℕ) (Φ : RowVector F n → ℂ) (c : RationalGL F n)
    (M : AdelicGL F n) : thetaSum F n Φ (AdelicGL.rational F n c * M) = thetaSum F n Φ M := by
  unfold thetaSum
  simp only [ratRow_mul_rational]
  rw [← (ratRowMulEquiv F n c).tsum_eq (fun C => if C = 0 then 0 else
    Φ (ratRow F n C * (M : Matrix (Fin n) (Fin n) (Adeles F))))]
  refine tsum_congr fun C => ?_
  simp only [ratRowMulEquiv_eq_zero_iff]

theorem thetaNorm_rational_mul (n : ℕ) (Φ : RowVector F n → ℂ) (c : RationalGL F n)
    (M : AdelicGL F n) : thetaNorm F n Φ (AdelicGL.rational F n c * M) = thetaNorm F n Φ M := by
  unfold thetaNorm
  simp only [ratRow_mul_rational]
  rw [← (ratRowMulEquiv F n c).tsum_eq (fun C => if C = 0 then 0 else
    ‖Φ (ratRow F n C * (M : Matrix (Fin n) (Fin n) (Adeles F)))‖ₑ)]
  refine tsum_congr fun C => ?_
  simp only [ratRowMulEquiv_eq_zero_iff]

/-! ### Measurability -/

theorem continuous_rowMul_term (n : ℕ) {Φ : RowVector F n → ℂ} (hΦ : Continuous Φ)
    (C : RatRow F n) :
    Continuous fun M : AdelicGL F n => Φ (ratRow F n C * (M : Matrix (Fin n) (Fin n) (Adeles F))) :=
  hΦ.comp (continuous_const.matrix_mul Units.continuous_val)

local notation "e" => GeneralLinearGroupPoints.adelicHomeomorph F

theorem stronglyMeasurable_thetaSum (n : ℕ) {Φ : RowVector F n → ℂ} (hΦ : Continuous Φ) :
    StronglyMeasurable fun g : Points F n => thetaSum F n Φ (e n g) := by
  refine StronglyMeasurable.tsum fun C => ?_
  by_cases hC : C = 0
  · simp only [hC, ite_true]
    exact stronglyMeasurable_const
  · simp only [hC, ite_false]
    exact ((continuous_rowMul_term F n hΦ C).comp (e n).continuous).stronglyMeasurable

theorem measurable_thetaNorm (n : ℕ) {Φ : RowVector F n → ℂ} (hΦ : Continuous Φ) :
    Measurable fun g : Points F n => thetaNorm F n Φ (e n g) := by
  refine (StronglyMeasurable.tsum fun C => ?_).measurable
  by_cases hC : C = 0
  · simp only [hC, ite_true]
    exact stronglyMeasurable_const
  · simp only [hC, ite_false]
    exact ((continuous_rowMul_term F n hΦ C).comp (e n).continuous).enorm.stronglyMeasurable

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
