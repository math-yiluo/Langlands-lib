import Langlands.Global.RankinSelberg.EqualAnalyticCover

/-! # Integrability on the regions `|det g| ≥ 1` and `|det g| < 1`

Fix a Siegel decomposition with compact `Q₁` and chamber constant `K`. Let `P` be continuous and
invariant under `GL_n(F)` with `|P(A(x) q)| ≤ C_c e^(-c D(x)) e^(A₀ |Σ x|)` for every `c ≥ 0`, and
let `V ≥ 0` be invariant with `V(A(x) q) ≤ V₀ e^(N D(x)) e^(β Σ x)`. Then, with `d = [F:ℚ]` and
`L(g) = log |det g|`,

* `∫_(L ≥ 0) |P| e^(σ L) V < ∞` if `σ d + β + A₀ ≤ -1` (`lintegral_region_ge_lt_top`);
* `∫_(L < 0) |P| e^(σ L) V < ∞` if `σ d + β - A₀ ≥ 1` (`lintegral_region_lt_lt_top`).

The theta factors `Θ⁺(Ψ, g)` and `Θ⁺(Ψ, ᵗg⁻¹)` satisfy the hypothesis on `V` with
`β = -N/n` and `β = N/n` for every integer `N > n [F:ℚ]` (`thetaNorm_chamber_le`,
`thetaNorm_iota_chamber_le`).
-/

noncomputable section
universe u
open NumberField MeasureTheory Set Langlands Langlands.Global Langlands.Automorphic
open scoped CategoryTheory.MonObj Matrix ENNReal

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

local instance regionsSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance regionsSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "e" => GeneralLinearGroupPoints.adelicHomeomorph F
local notation "E" => GeneralLinearGroupPoints.adelicEquiv F

/-- The elementary inequality behind the region bounds. -/
theorem region_real {p v C V₀ N D S σ d β A₀ lq ℓ₀ B₀ : ℝ} (hv0 : 0 ≤ v)
    (hC : 0 ≤ C) (hV₀ : 0 ≤ V₀)
    (hp : p ≤ C * Real.exp (-((N + 1) * D)) * Real.exp (A₀ * |S|))
    (hv : v ≤ V₀ * Real.exp (N * D) * Real.exp (β * S)) (hlq : |lq| ≤ ℓ₀)
    (hexp : A₀ * |S| + (σ * d + β) * S ≤ -|S| + B₀) :
    p * Real.exp (σ * (d * S + lq)) * v ≤
      C * V₀ * Real.exp (|σ| * ℓ₀ + B₀) * Real.exp (-D) * Real.exp (-|S|) := by
  have h1 : p * Real.exp (σ * (d * S + lq)) * v ≤
      (C * Real.exp (-((N + 1) * D)) * Real.exp (A₀ * |S|)) * Real.exp (σ * (d * S + lq)) *
        (V₀ * Real.exp (N * D) * Real.exp (β * S)) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le) hv hv0 (by positivity)
  have h2 : (C * Real.exp (-((N + 1) * D)) * Real.exp (A₀ * |S|)) * Real.exp (σ * (d * S + lq)) *
      (V₀ * Real.exp (N * D) * Real.exp (β * S)) = C * V₀ *
        Real.exp (-((N + 1) * D) + A₀ * |S| + σ * (d * S + lq) + N * D + β * S) := by
    simp only [Real.exp_add]
    ring
  have hσ : σ * lq ≤ |σ| * ℓ₀ := by
    calc σ * lq ≤ |σ * lq| := le_abs_self _
      _ = |σ| * |lq| := abs_mul _ _
      _ ≤ |σ| * ℓ₀ := mul_le_mul_of_nonneg_left hlq (abs_nonneg _)
  have h3 : -((N + 1) * D) + A₀ * |S| + σ * (d * S + lq) + N * D + β * S ≤
      |σ| * ℓ₀ + B₀ + -D + -|S| := by nlinarith
  have h4 : C * V₀ * Real.exp (|σ| * ℓ₀ + B₀ + -D + -|S|) =
      C * V₀ * Real.exp (|σ| * ℓ₀ + B₀) * Real.exp (-D) * Real.exp (-|S|) := by
    simp only [Real.exp_add]
    ring
  rw [← h4]
  exact h1.trans (h2 ▸ mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h3) (by positivity))

/-- Chamber decay of a function on `GL_n(𝔸)`, transported to points. -/
def PointDecay (Q₁ : Set (AdelicGL F n)) (K : ℝ) (P : Points F n → ℂ) (A₀ : ℝ) : Prop :=
  0 ≤ A₀ ∧ ∀ c : ℝ, 0 ≤ c → ∃ C : ℝ, ∀ x : Fin n → ℝ, CuspidalL2.Chamber (K + 2) x →
    ∀ q ∈ Q₁, ‖P ((e n).symm (torusA (F := F) x * q))‖ ≤
      C * Real.exp (-(c * spread x)) * Real.exp (A₀ * |∑ i, x i|)

theorem detNorm_symm (M : AdelicGL F n) : detNorm F n ((e n).symm M) = absDet F n M := by
  show absDet F n (e n ((e n).symm M)) = _
  rw [ContinuousMulEquiv.apply_symm_apply]

/-- The function `|P| e^(σ L) V` on `{L ≥ 0}`. -/
def regionGe (P : Points F n → ℂ) (σ : ℝ) (V : Points F n → ℝ≥0∞) (g : Points F n) : ℝ≥0∞ :=
  {g : Points F n | 0 ≤ Real.log (detNorm F n g)}.indicator
    (fun g => ‖P g‖ₑ * ENNReal.ofReal (Real.exp (σ * Real.log (detNorm F n g))) * V g) g

/-- The function `|P| e^(σ L) V` on `{L < 0}`. -/
def regionLt (P : Points F n → ℂ) (σ : ℝ) (V : Points F n → ℝ≥0∞) (g : Points F n) : ℝ≥0∞ :=
  {g : Points F n | Real.log (detNorm F n g) < 0}.indicator
    (fun g => ‖P g‖ₑ * ENNReal.ofReal (Real.exp (σ * Real.log (detNorm F n g))) * V g) g

theorem measurable_log_detNorm (n : ℕ) :
    Measurable fun g : Points F n => Real.log (detNorm F n g) :=
  Real.measurable_log.comp (UnequalAnalytic.continuous_detNorm F n).measurable

theorem measurable_regionGe {P : Points F n → ℂ} (hP : Continuous P) (σ : ℝ)
    {V : Points F n → ℝ≥0∞} (hV : Measurable V) : Measurable (regionGe P σ V) :=
  (((hP.measurable.enorm).mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (measurable_log_detNorm n))))).mul hV).indicator
    (measurableSet_le measurable_const (measurable_log_detNorm n))

theorem measurable_regionLt {P : Points F n → ℂ} (hP : Continuous P) (σ : ℝ)
    {V : Points F n → ℝ≥0∞} (hV : Measurable V) : Measurable (regionLt P σ V) :=
  (((hP.measurable.enorm).mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (measurable_log_detNorm n))))).mul hV).indicator
    (measurableSet_lt (measurable_log_detNorm n) measurable_const)

theorem enorm_mul_ofReal_le {p : ℂ} {a b : ℝ} {v : ℝ≥0∞} (hv : v ≤ ENNReal.ofReal b)
    (ha : 0 ≤ a) : ‖p‖ₑ * ENNReal.ofReal a * v ≤ ENNReal.ofReal (‖p‖ * a * b) := by
  calc ‖p‖ₑ * ENNReal.ofReal a * v ≤ ENNReal.ofReal ‖p‖ * ENNReal.ofReal a * ENNReal.ofReal b := by
        rw [ofReal_norm]
        gcongr
    _ = ENNReal.ofReal (‖p‖ * a * b) := by
        rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]

theorem regionGe_rational_mul {P : Points F n → ℂ}
    (hPr : ∀ (c : RationalGroupPoints F (Scheme F n)) (g : Points F n),
      P (AdelicGroupPoints.rational F (Scheme F n) c * g) = P g) (σ : ℝ) {V : Points F n → ℝ≥0∞}
    (hVr : ∀ (c : RationalGroupPoints F (Scheme F n)) (g : Points F n),
      V (AdelicGroupPoints.rational F (Scheme F n) c * g) = V g)
    (c : RationalGroupPoints F (Scheme F n)) (g : Points F n) :
    regionGe P σ V (AdelicGroupPoints.rational F (Scheme F n) c * g) = regionGe P σ V g := by
  simp only [regionGe, Set.indicator, Set.mem_ofPred_eq, UnequalAnalytic.detNorm_rational_mul,
    hPr, hVr]

theorem regionLt_rational_mul {P : Points F n → ℂ}
    (hPr : ∀ (c : RationalGroupPoints F (Scheme F n)) (g : Points F n),
      P (AdelicGroupPoints.rational F (Scheme F n) c * g) = P g) (σ : ℝ) {V : Points F n → ℝ≥0∞}
    (hVr : ∀ (c : RationalGroupPoints F (Scheme F n)) (g : Points F n),
      V (AdelicGroupPoints.rational F (Scheme F n) c * g) = V g)
    (c : RationalGroupPoints F (Scheme F n)) (g : Points F n) :
    regionLt P σ V (AdelicGroupPoints.rational F (Scheme F n) c * g) = regionLt P σ V g := by
  simp only [regionLt, Set.indicator, Set.mem_ofPred_eq, UnequalAnalytic.detNorm_rational_mul,
    hPr, hVr]

theorem log_detNorm_symm_torusA (x : Fin n → ℝ) (q : AdelicGL F n) :
    Real.log (detNorm F n ((e n).symm (torusA (F := F) x * q))) =
      Module.finrank ℚ F * ∑ i, x i + Real.log (absDet F n q) := by
  rw [detNorm_symm, UnequalAnalytic.log_absDet_torInf_mul]

/-- **Finiteness on `|det g| ≥ 1`.** -/
theorem lintegral_region_ge_lt_top {Q₁ : Set (AdelicGL F n)} {K : ℝ} (hQ₁ : IsCompact Q₁)
    (hdec : ∀ g : AdelicGL F n, ∃ (c : RationalGL F n) (x : Fin n → ℝ) (q : AdelicGL F n),
        q ∈ Q₁ ∧ AdelicGL.rational F n c * g = torusA (F := F) x * q ∧
          CuspidalL2.Chamber K x)
    {ℓ₀ : ℝ} (hℓ₀0 : 0 ≤ ℓ₀) (hℓ₀ : ∀ q ∈ Q₁, |Real.log (absDet F n q)| ≤ ℓ₀)
    {P : Points F n → ℂ} (hPc : Continuous P)
    (hPr : ∀ (c : RationalGroupPoints F (Scheme F n)) (g : Points F n),
      P (AdelicGroupPoints.rational F (Scheme F n) c * g) = P g)
    {A₀ : ℝ} (hPd : PointDecay Q₁ K P A₀)
    {V : Points F n → ℝ≥0∞} (hVm : Measurable V)
    (hVr : ∀ (c : RationalGroupPoints F (Scheme F n)) (g : Points F n),
      V (AdelicGroupPoints.rational F (Scheme F n) c * g) = V g)
    {N β V₀ : ℝ} (hN : 0 ≤ N) (hV₀ : 0 ≤ V₀)
    (hV : ∀ x : Fin n → ℝ, ∀ q ∈ Q₁, V ((e n).symm (torusA (F := F) x * q)) ≤
      ENNReal.ofReal (V₀ * Real.exp (N * spread x) * Real.exp (β * ∑ i, x i)))
    {σ : ℝ} (hσ : σ * Module.finrank ℚ F + β + A₀ ≤ -1) :
    ∫⁻ y, regionGe P σ V (Quotient.out y)
      ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n) < ⊤ := by
  have hd0 : (0 : ℝ) < Module.finrank ℚ F := Nat.cast_pos.mpr Module.finrank_pos
  obtain ⟨hA₀, hPdec⟩ := hPd
  obtain ⟨C, hC⟩ := hPdec (N + 1) (by linarith)
  refine lintegral_quotient_lt_top_of_siegel hQ₁ hdec (regionGe P σ V)
    (measurable_regionGe hPc σ hVm) (regionGe_rational_mul hPr σ hVr)
    (|C| * V₀ * Real.exp (|σ| * ℓ₀ +
      (|σ * Module.finrank ℚ F + β| + A₀ + 1) * (ℓ₀ / Module.finrank ℚ F))) fun x hx q hq => ?_
  have hdet := log_detNorm_symm_torusA (F := F) x q
  unfold regionGe
  by_cases hL : 0 ≤ Real.log (detNorm F n ((e n).symm (torusA (F := F) x * q)))
  · rw [Set.indicator_of_mem (show (e n).symm (torusA (F := F) x * q) ∈
      {g : Points F n | 0 ≤ Real.log (detNorm F n g)} from hL)]
    refine (enorm_mul_ofReal_le (hV x q hq) (Real.exp_pos _).le).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [hdet] at hL ⊢
    have hlq := hℓ₀ q hq
    have hS : -(ℓ₀ / Module.finrank ℚ F) ≤ ∑ i, x i := by
      have h1 : -ℓ₀ ≤ Module.finrank ℚ F * ∑ i, x i := by linarith [(abs_le.1 hlq).2]
      rw [← neg_div, div_le_iff₀ hd0]
      linarith
    have hexp := exponent_le_of_ge (S := ∑ i, x i) (A₀ := A₀)
      (α := σ * Module.finrank ℚ F + β) (by positivity) hA₀ hS hσ
    have hp : ‖P ((e n).symm (torusA (F := F) x * q))‖ ≤
        |C| * Real.exp (-((N + 1) * spread x)) * Real.exp (A₀ * |∑ i, x i|) :=
      (hC x hx q hq).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
        (Real.exp_pos _).le) (Real.exp_pos _).le)
    exact region_real (by positivity) (abs_nonneg C) hV₀ hp le_rfl hlq hexp
  · rw [Set.indicator_of_notMem (show (e n).symm (torusA (F := F) x * q) ∉
      {g : Points F n | 0 ≤ Real.log (detNorm F n g)} from hL)]
    exact zero_le

/-- **Finiteness on `|det g| < 1`.** -/
theorem lintegral_region_lt_lt_top {Q₁ : Set (AdelicGL F n)} {K : ℝ} (hQ₁ : IsCompact Q₁)
    (hdec : ∀ g : AdelicGL F n, ∃ (c : RationalGL F n) (x : Fin n → ℝ) (q : AdelicGL F n),
        q ∈ Q₁ ∧ AdelicGL.rational F n c * g = torusA (F := F) x * q ∧
          CuspidalL2.Chamber K x)
    {ℓ₀ : ℝ} (hℓ₀0 : 0 ≤ ℓ₀) (hℓ₀ : ∀ q ∈ Q₁, |Real.log (absDet F n q)| ≤ ℓ₀)
    {P : Points F n → ℂ} (hPc : Continuous P)
    (hPr : ∀ (c : RationalGroupPoints F (Scheme F n)) (g : Points F n),
      P (AdelicGroupPoints.rational F (Scheme F n) c * g) = P g)
    {A₀ : ℝ} (hPd : PointDecay Q₁ K P A₀)
    {V : Points F n → ℝ≥0∞} (hVm : Measurable V)
    (hVr : ∀ (c : RationalGroupPoints F (Scheme F n)) (g : Points F n),
      V (AdelicGroupPoints.rational F (Scheme F n) c * g) = V g)
    {N β V₀ : ℝ} (hN : 0 ≤ N) (hV₀ : 0 ≤ V₀)
    (hV : ∀ x : Fin n → ℝ, ∀ q ∈ Q₁, V ((e n).symm (torusA (F := F) x * q)) ≤
      ENNReal.ofReal (V₀ * Real.exp (N * spread x) * Real.exp (β * ∑ i, x i)))
    {σ : ℝ} (hσ : 1 ≤ σ * Module.finrank ℚ F + β - A₀) :
    ∫⁻ y, regionLt P σ V (Quotient.out y)
      ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n) < ⊤ := by
  have hd0 : (0 : ℝ) < Module.finrank ℚ F := Nat.cast_pos.mpr Module.finrank_pos
  obtain ⟨hA₀, hPdec⟩ := hPd
  obtain ⟨C, hC⟩ := hPdec (N + 1) (by linarith)
  refine lintegral_quotient_lt_top_of_siegel hQ₁ hdec (regionLt P σ V)
    (measurable_regionLt hPc σ hVm) (regionLt_rational_mul hPr σ hVr)
    (|C| * V₀ * Real.exp (|σ| * ℓ₀ +
      (|σ * Module.finrank ℚ F + β| + A₀ + 1) * (ℓ₀ / Module.finrank ℚ F))) fun x hx q hq => ?_
  have hdet := log_detNorm_symm_torusA (F := F) x q
  unfold regionLt
  by_cases hL : Real.log (detNorm F n ((e n).symm (torusA (F := F) x * q))) < 0
  · rw [Set.indicator_of_mem (show (e n).symm (torusA (F := F) x * q) ∈
      {g : Points F n | Real.log (detNorm F n g) < 0} from hL)]
    refine (enorm_mul_ofReal_le (hV x q hq) (Real.exp_pos _).le).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [hdet] at hL ⊢
    have hlq := hℓ₀ q hq
    have hS : ∑ i, x i ≤ ℓ₀ / Module.finrank ℚ F := by
      have h1 : Module.finrank ℚ F * ∑ i, x i ≤ ℓ₀ := by linarith [(abs_le.1 hlq).1]
      rw [le_div_iff₀ hd0]
      linarith
    have hexp := exponent_le_of_le (S := ∑ i, x i) (A₀ := A₀)
      (α := σ * Module.finrank ℚ F + β) (by positivity) hA₀ hS hσ
    have hp : ‖P ((e n).symm (torusA (F := F) x * q))‖ ≤
        |C| * Real.exp (-((N + 1) * spread x)) * Real.exp (A₀ * |∑ i, x i|) :=
      (hC x hx q hq).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
        (Real.exp_pos _).le) (Real.exp_pos _).le)
    exact region_real (by positivity) (abs_nonneg C) hV₀ hp le_rfl hlq hexp
  · rw [Set.indicator_of_notMem (show (e n).symm (torusA (F := F) x * q) ∉
      {g : Points F n | Real.log (detNorm F n g) < 0} from hL)]
    exact zero_le

/-! ### Theta factors -/

omit [NumberField F] in
theorem torInf_zero' : torInf F n 0 = 1 := by
  have h := torInf_add F n 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem torusA_neg_mul (x : Fin n → ℝ) : torusA (F := F) (-x) * torusA (F := F) x = 1 := by
  simp only [torusA, ← map_mul, ← torInf_add, neg_add_cancel, torInf_zero', map_one]

theorem inverseTranspose_torusA (x : Fin n → ℝ) :
    GeneralLinear.inverseTranspose n (Adeles F) (torusA (F := F) x) = torusA (F := F) (-x) := by
  apply Units.ext
  rw [inverseTranspose_val, inv_eq_of_mul_eq_one_left (torusA_neg_mul (F := F) x)]
  simp only [torusA, ofInfinite_torInf_val, Matrix.diagonal_transpose]

theorem le_of_spread (x : Fin n → ℝ) (j : Fin n) :
    (∑ i, x i) / n - spread x ≤ x j := by
  have h1 : |x j - (∑ i, x i) / n| ≤ spread x :=
    Finset.single_le_sum (f := fun i => |x i - (∑ i, x i) / n|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ j)
  have h2 := neg_abs_le (x j - (∑ i, x i) / n)
  linarith

/-- **The theta factor in Siegel coordinates.** -/
theorem thetaNorm_chamber_le {Ψ : RowVector F n → ℂ} (hΨ : IsRowDominated F n Ψ)
    {Q₁ : Set (AdelicGL F n)} (hQ₁ : IsCompact Q₁) (N : ℕ) (hN : n * Module.finrank ℚ F < N) :
    ∃ V₀ : ℝ, 0 ≤ V₀ ∧ ∀ x : Fin n → ℝ, ∀ q ∈ Q₁,
      thetaNorm F n Ψ (E n ((e n).symm (torusA (F := F) x * q))) ≤
        ENNReal.ofReal (V₀ * Real.exp (N * spread x) *
          Real.exp (-((N : ℝ) / n) * ∑ i, x i)) := by
  obtain ⟨V₀, hV₀, h⟩ := exists_thetaNorm_le F n hΨ hQ₁ N hN
  refine ⟨V₀, hV₀, fun x q hq => ?_⟩
  have hE : E n ((e n).symm (torusA (F := F) x * q)) = torusA (F := F) x * q :=
    (e n).apply_symm_apply _
  rw [hE]
  refine (h x ((∑ i, x i) / n - spread x) (le_of_spread x) q hq).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **The transposed-inverse theta factor in Siegel coordinates.** -/
theorem thetaNorm_iota_chamber_le {Ψ : RowVector F n → ℂ} (hΨ : IsRowDominated F n Ψ)
    {Q₁ : Set (AdelicGL F n)} (hQ₁ : IsCompact Q₁) (N : ℕ) (hN : n * Module.finrank ℚ F < N) :
    ∃ V₀ : ℝ, 0 ≤ V₀ ∧ ∀ x : Fin n → ℝ, ∀ q ∈ Q₁,
      thetaNorm F n Ψ (E n (iota F n ((e n).symm (torusA (F := F) x * q)))) ≤
        ENNReal.ofReal (V₀ * Real.exp (N * spread x) *
          Real.exp (((N : ℝ) / n) * ∑ i, x i)) := by
  have hQ' : IsCompact (GeneralLinear.inverseTranspose n (Adeles F) '' Q₁) :=
    hQ₁.image (GeneralLinear.continuous_inverseTranspose n (Adeles F))
  obtain ⟨V₀, hV₀, h⟩ := exists_thetaNorm_le F n hΨ hQ' N hN
  refine ⟨V₀, hV₀, fun x q hq => ?_⟩
  have hE : E n (iota F n ((e n).symm (torusA (F := F) x * q))) =
      torusA (F := F) (-x) * GeneralLinear.inverseTranspose n (Adeles F) q := by
    rw [UnequalAnalytic.adelicEquiv_iota]
    change GeneralLinear.inverseTranspose n (Adeles F)
      ((e n) ((e n).symm (torusA (F := F) x * q))) = _
    rw [ContinuousMulEquiv.apply_symm_apply, map_mul, inverseTranspose_torusA]
  rw [hE]
  have ht : ∀ j, -((∑ i, x i) / n) - spread x ≤ (-x) j := by
    intro j
    have h1 : |x j - (∑ i, x i) / n| ≤ spread x :=
      Finset.single_le_sum (f := fun i => |x i - (∑ i, x i) / n|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ j)
    have h2 := le_abs_self (x j - (∑ i, x i) / n)
    simp only [Pi.neg_apply]
    linarith
  refine (h (-x) _ ht _ ⟨q, hq, rfl⟩).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
