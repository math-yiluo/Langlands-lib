import Langlands.Algebra.FormalExponentialStraightening
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Evaluation of bounded homogeneous word series in an ultrametric algebra -/

noncomputable section

namespace Langlands.CyclicWords

open FreeMonoid PowerSeries Function Filter Set Metric Langlands.FormalPowerSeries
open scoped _root_.Topology

variable {F A : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]
  [NormedRing A] [NormedAlgebra F A] [IsUltrametricDist A]

local notation "Series" => PowerSeries (WordPolynomial F)
local notation "K" => max (1 : ℝ) ‖(1 : A)‖

private def assignLetter (x : A × A) (b : Bool) : A := if b then x.2 else x.1

private def wordEval (x : A × A) : Word →* A := FreeMonoid.lift (assignLetter x)

/-- Evaluate the first letter at `x.1` and the second letter at `x.2`. -/
def polynomialEval (x : A × A) : WordPolynomial F →ₐ[F] A := MonoidAlgebra.lift F A Word (wordEval x)

omit [IsUltrametricDist F] [IsUltrametricDist A] in
@[simp] theorem polynomialEval_letter (x : A × A) (b : Bool) :
    polynomialEval (F := F) x (letter b) = if b then x.2 else x.1 := by
  simp [polynomialEval, letter, wordEval, assignLetter]

omit [IsUltrametricDist A] in
private theorem norm_assignLetter_le (x : A × A) (b : Bool) : ‖assignLetter x b‖ ≤ ‖x‖ := by
  cases b <;> simp [assignLetter, Prod.norm_def]

omit [IsUltrametricDist A] in
private theorem norm_assignLetter_sub_le (x y : A × A) (b : Bool) :
    ‖assignLetter x b - assignLetter y b‖ ≤ ‖x - y‖ := by
  cases b <;> simp [assignLetter, Prod.norm_def]

omit [IsUltrametricDist A] in
private theorem norm_wordEval_le (x : A × A) {r : ℝ} (hx : ‖x‖ ≤ r) (w : Word) :
    ‖wordEval x w‖ ≤ K * r ^ w.length := by
  have hr := (norm_nonneg _).trans hx
  induction w using FreeMonoid.recOn with
  | one => simp
  | of_mul b w ih =>
    rw [map_mul, show wordEval x (of b) = assignLetter x b from FreeMonoid.lift_eval_of _ _,
      length_mul, length_of, pow_add, pow_one]
    calc
      _ ≤ ‖assignLetter x b‖ * ‖wordEval x w‖ := norm_mul_le _ _
      _ ≤ r * (K * r ^ w.length) := mul_le_mul ((norm_assignLetter_le x b).trans hx) ih (norm_nonneg _) hr
      _ = _ := by ring

private theorem norm_wordEval_sub_le (x y : A × A) {r : ℝ} (hr : 0 < r) (hx : ‖x‖ ≤ r)
    (hy : ‖y‖ ≤ r) (w : Word) :
    ‖wordEval x w - wordEval y w‖ ≤ (K / r) * r ^ w.length * ‖x - y‖ := by
  have hK : 0 ≤ K := zero_le_one.trans (le_max_left _ _)
  induction w using FreeMonoid.recOn with
  | one => simp only [map_one, sub_self, norm_zero]; positivity
  | of_mul b w ih =>
    let a := assignLetter x b
    let a' := assignLetter y b
    let p := wordEval x w
    let p' := wordEval y w
    have hL := (norm_assignLetter_le y b).trans hy
    have hD := norm_assignLetter_sub_le x y b
    have hP := norm_wordEval_le x hx w
    have hEq : wordEval x (of b * w) - wordEval y (of b * w) = (a - a') * p + a' * (p - p') := by
      simp only [wordEval, map_mul, FreeMonoid.lift_eval_of]
      change a * p - a' * p' = _
      rw [sub_mul, mul_sub]
      abel
    rw [hEq, length_mul, length_of, pow_add, pow_one]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    apply max_le
    · calc
        _ ≤ ‖a - a'‖ * ‖p‖ := norm_mul_le _ _
        _ ≤ ‖x - y‖ * (K * r ^ w.length) := mul_le_mul hD hP (norm_nonneg _) (norm_nonneg _)
        _ = _ := by field_simp
    · calc
        _ ≤ ‖a'‖ * ‖p - p'‖ := norm_mul_le _ _
        _ ≤ r * ((K / r) * r ^ w.length * ‖x - y‖) := mul_le_mul hL ih (norm_nonneg _) hr.le
        _ = _ := by ring

omit [IsUltrametricDist F] in
private theorem norm_polynomialEval_le {n : ℕ} {c r : ℝ} {p : WordPolynomial F}
    (hp : WordPolynomialControl n c p) {x : A × A} (hx : ‖x‖ ≤ r) :
    ‖polynomialEval x p‖ ≤ K * c * r ^ n := by
  classical
  have hr := (norm_nonneg _).trans hx
  rw [polynomialEval, MonoidAlgebra.lift_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity [hp.nonneg])
  intro w hw
  change ‖p.coeff w • wordEval x w‖ ≤ K * c * r ^ n
  have hwn : w.length = n := not_ne_iff.mp fun h => (Finsupp.mem_support_iff.mp hw) (hp.graded w h)
  rw [norm_smul]
  calc
    _ ≤ c * (K * r ^ w.length) := mul_le_mul (hp.norm_le w) (norm_wordEval_le x hx w) (norm_nonneg _) hp.nonneg
    _ = _ := by rw [hwn]; ring

omit [IsUltrametricDist F] in
private theorem norm_polynomialEval_sub_le {n : ℕ} {c r : ℝ} {p : WordPolynomial F}
    (hp : WordPolynomialControl n c p) {x y : A × A} (hr : 0 < r) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖polynomialEval x p - polynomialEval y p‖ ≤ (K * c / r) * r ^ n * ‖x - y‖ := by
  classical
  rw [polynomialEval, MonoidAlgebra.lift_apply, polynomialEval, MonoidAlgebra.lift_apply]
  unfold Finsupp.sum
  rw [← Finset.sum_sub_distrib]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity [hp.nonneg])
  intro w hw
  change ‖p.coeff w • wordEval x w - p.coeff w • wordEval y w‖ ≤ (K * c / r) * r ^ n * ‖x - y‖
  have hwn : w.length = n := not_ne_iff.mp fun h => (Finsupp.mem_support_iff.mp hw) (hp.graded w h)
  rw [← smul_sub, norm_smul]
  calc
    _ ≤ c * ((K / r) * r ^ w.length * ‖x - y‖) :=
      mul_le_mul (hp.norm_le w) (norm_wordEval_sub_le x y hr hx hy w) (norm_nonneg _) hp.nonneg
    _ = _ := by rw [hwn]; ring

variable [CompleteSpace A]

/-- Sum the evaluations of the homogeneous coefficients of the word series. -/
def seriesEval (x : A × A) (f : Series) : A := ∑' n : ℕ, polynomialEval x (coeff n f)

omit [CompleteSpace A] [IsUltrametricDist F] in
private theorem summable_norm_eval {c r : ℝ} {f : Series} (hf : WordSeriesControl c f)
    {x : A × A} (hx : ‖x‖ ≤ r) (hr : r < 1) :
    Summable fun n : ℕ => ‖polynomialEval x (coeff n f)‖ :=
  ((summable_geometric_of_lt_one ((norm_nonneg _).trans hx) hr).mul_left (K * c)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => norm_polynomialEval_le (hf n) hx)

omit [IsUltrametricDist F] in
private theorem summable_eval {c r : ℝ} {f : Series} (hf : WordSeriesControl c f)
    {x : A × A} (hx : ‖x‖ ≤ r) (hr : r < 1) : Summable fun n : ℕ => polynomialEval x (coeff n f) :=
  (summable_norm_eval hf hx hr).of_norm

omit [IsUltrametricDist F] [IsUltrametricDist A] [CompleteSpace A] in
@[simp] theorem seriesEval_monomial (x : A × A) (n : ℕ) (p : WordPolynomial F) :
    seriesEval (F := F) x (PowerSeries.monomial n p) = polynomialEval x p := by
  unfold seriesEval
  rw [tsum_eq_single n]
  · rw [coeff_monomial_same]
  · intro m hm
    rw [coeff_monomial, ite_eq_right hm, map_zero]

omit [IsUltrametricDist F] [IsUltrametricDist A] [CompleteSpace A] in
@[simp] theorem seriesEval_one (x : A × A) : seriesEval (F := F) x 1 = 1 := by
  have h := seriesEval_monomial x 0 (1 : WordPolynomial F)
  simpa only [PowerSeries.monomial_zero_eq_C_apply, map_one] using h

omit [IsUltrametricDist F] [IsUltrametricDist A] [CompleteSpace A] in
@[simp] theorem seriesEval_letter (x : A × A) (b : Bool) :
    seriesEval (F := F) x (seriesLetter b) = if b then x.2 else x.1 := by
  simp [seriesLetter]

variable {x : A × A} {a b r : ℝ} {f g : PowerSeries (WordPolynomial F)}

omit [IsUltrametricDist F] in
theorem seriesEval_add (hx : ‖x‖ ≤ r) (hr : r < 1) (hf : WordSeriesControl a f) (hg : WordSeriesControl b g) :
    seriesEval (F := F) x (f + g) = seriesEval (F := F) x f + seriesEval (F := F) x g := by
  simp only [seriesEval, map_add]
  exact (summable_eval hf hx hr).tsum_add (summable_eval hg hx hr)

omit [IsUltrametricDist F] in
theorem seriesEval_sub (hx : ‖x‖ ≤ r) (hr : r < 1) (hf : WordSeriesControl a f) (hg : WordSeriesControl b g) :
    seriesEval (F := F) x (f - g) = seriesEval (F := F) x f - seriesEval (F := F) x g := by
  simp only [seriesEval, map_sub]
  exact (summable_eval hf hx hr).tsum_sub (summable_eval hg hx hr)

omit [IsUltrametricDist F] in
theorem seriesEval_smul (hx : ‖x‖ ≤ r) (hr : r < 1) (hf : WordSeriesControl a f) (c : F) :
    seriesEval (F := F) x (c • f) = c • seriesEval (F := F) x f := by
  simp only [seriesEval, coeff_smul, map_smul]
  exact (summable_eval hf hx hr).tsum_const_smul c

omit [IsUltrametricDist F] in
theorem seriesEval_mul (hx : ‖x‖ ≤ r) (hr : r < 1) (hf : WordSeriesControl a f) (hg : WordSeriesControl b g) :
    seriesEval (F := F) x (f * g) = seriesEval (F := F) x f * seriesEval (F := F) x g := by
  simp only [seriesEval, coeff_mul, map_sum, map_mul]
  exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (summable_norm_eval hf hx hr) (summable_norm_eval hg hx hr)).symm

theorem seriesEval_pow (hx : ‖x‖ ≤ r) (hr : r < 1) (hf : WordSeriesControl a f) (n : ℕ) :
    seriesEval (F := F) x (f ^ n) = seriesEval (F := F) x f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, seriesEval_mul hx hr (hf.pow _) hf, ih]

omit [IsUltrametricDist F] in
private theorem seriesEval_finsetSum {ι : Type*} (hx : ‖x‖ ≤ r) (hr : r < 1)
    (I : Finset ι) (p : ι → Series) (h : ∀ i ∈ I, ∃ c : ℝ, WordSeriesControl c (p i)) :
    seriesEval (F := F) x (∑ i ∈ I, p i) = ∑ i ∈ I, seriesEval (F := F) x (p i) := by
  simp only [seriesEval, map_sum]
  apply Summable.tsum_finsetSum
  intro i hi
  obtain ⟨c, hc⟩ := h i hi
  exact summable_eval hc hx hr

omit [IsUltrametricDist F] [CompleteSpace A] in
/-- A series vanishing below `n` has evaluation bounded by the corresponding geometric term. -/
theorem norm_seriesEval_le_of_vanishesBelow (hx : ‖x‖ ≤ r) (hr : r < 1)
    (hf : WordSeriesControl a f) {n : ℕ} (hn : VanishesBelow n f) : ‖seriesEval (F := F) x f‖ ≤ K * a * r ^ n := by
  have hr₀ := (norm_nonneg _).trans hx
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro m
  by_cases hm : m < n
  · rw [hn m hm, map_zero, norm_zero]
    positivity [hf.nonneg]
  · exact (norm_polynomialEval_le (hf m) hx).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr₀ hr.le (not_lt.mp hm)) (by positivity [hf.nonneg]))

omit [IsUltrametricDist F] in
/-- The evaluation of a bounded word series is Lipschitz on a fixed closed pair ball of radius less than one. -/
theorem norm_seriesEval_sub_le {y : A × A} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (hr₀ : 0 < r) (hr : r < 1)
    (hf : WordSeriesControl a f) : ‖seriesEval (F := F) x f - seriesEval (F := F) y f‖ ≤ (K * a / r) * ‖x - y‖ := by
  rw [seriesEval, seriesEval, ← (summable_eval hf hx hr).tsum_sub (summable_eval hf hy hr)]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro n
  refine (norm_polynomialEval_sub_le (hf n) hr₀ hx hy).trans ?_
  have hn := pow_le_one₀ hr₀.le hr.le (n := n)
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity [hf.nonneg]) hn) (norm_nonneg _)

/-- Evaluate a formal unit of constant coefficient one using the convergent series for both it and its inverse. -/
def seriesEvalUnit (hx : ‖x‖ ≤ r) (hr : r < 1) (u : Seriesˣ) (hu₀ : constantCoeff (u : Series) = 1)
    (hu : WordSeriesControl 1 (u : Series)) : Aˣ :=
  let U := seriesEval (F := F) x (u : Series)
  let V := seriesEval (F := F) x (↑u⁻¹ : Series)
  have hV := WordSeriesControl.inv_unit u hu₀ hu
  ⟨U, V, by rw [← seriesEval_mul hx hr hu hV, Units.mul_inv, seriesEval_one],
    by rw [← seriesEval_mul hx hr hV hu, Units.inv_mul, seriesEval_one]⟩

variable [CharZero F]

/-- On sufficiently small pair balls, evaluating the formal exponential of a bounded
homogeneous word series with zero constant term gives the normed algebra exponential. -/
def WordSeriesExponentialEvaluationStatement (F A : Type*) [NontriviallyNormedField F]
    [IsUltrametricDist F] [CharZero F] [NormedRing A] [NormedAlgebra F A] [IsUltrametricDist A]
    [CompleteSpace A] : Prop :=
  ∀ (x : A × A) (r c : ℝ), ‖x‖ ≤ r → r < 1 → max (1 : ℝ) ‖(1 : A)‖ * r < 1 → c ≤ 1 →
    ∀ f : PowerSeries (WordPolynomial F), WordSeriesControl c f → VanishesBelow 1 f →
      (∀ k : ℕ, 0 < k → ‖((k.factorial : F)⁻¹)‖ * c ^ k ≤ c) →
        seriesEval (F := F) x (formalExponential F f) = NormedSpace.exp (seriesEval (F := F) x f)

set_option maxHeartbeats 2300000 in
theorem wordSeriesExponentialEvaluation : WordSeriesExponentialEvaluationStatement F A := by
  intro x r c hx hr hKr hc f hf hvan hFac
  have hr₀ := (norm_nonneg _).trans hx
  let E := formalExponential F f
  let P (N : ℕ) := exponentialPartial F N f
  have hTerm (k : ℕ) : WordSeriesControl 1 ((((k.factorial : F)⁻¹)) • f ^ k) := by
    by_cases hk : k = 0
    · subst k; simpa using (WordSeriesControl.one (F := F))
    · exact ((hf.pow k).smul _).mono ((hFac k (Nat.pos_of_ne_zero hk)).trans hc)
  have hE : WordSeriesControl 1 E := by
    have h := ((WordSeriesControl.exponentialControl _ _ hf hFac).mono hc).add (WordSeriesControl.one (F := F))
    simpa only [sub_add_cancel] using h
  have hP (N : ℕ) : WordSeriesControl 1 (P N) := by
    intro n
    change WordPolynomialControl n 1 (coeff n (∑ k ∈ Finset.range (N + 1), ((k.factorial : F)⁻¹) • f ^ k))
    rw [map_sum]
    exact WordPolynomialControl.finsetSum zero_le_one fun k _ => hTerm k n
  have hExplicit (N : ℕ) : seriesEval (F := F) x (P N) =
      ∑ k ∈ Finset.range (N + 1), ((k.factorial : F)⁻¹) • seriesEval (F := F) x f ^ k := by
    unfold P exponentialPartial
    rw [seriesEval_finsetSum hx hr _ _ (fun k _ => ⟨1, hTerm k⟩)]
    apply Finset.sum_congr rfl
    intro k _
    rw [seriesEval_smul hx hr (hf.pow k), seriesEval_pow hx hr hf]
  have hTail (N : ℕ) : VanishesBelow (N + 1) (P N - E) := fun n hn => by
    rw [map_sub]
    change coeff n (P N) - coeff n (formalExponential F f) = 0
    rw [coeff_formalExponential_of_le F hvan (n := n) (N := N) (by omega), sub_self]
  have hNorm (N : ℕ) : ‖seriesEval (F := F) x (P N) - seriesEval (F := F) x E‖ ≤ K * r ^ (N + 1) := by
    rw [← seriesEval_sub hx hr (hP N) hE]
    simpa only [mul_one] using norm_seriesEval_le_of_vanishesBelow hx hr ((hP N).sub hE) (hTail N)
  have hLim : Tendsto (fun N : ℕ => seriesEval (F := F) x (P N)) atTop (𝓝 (seriesEval (F := F) x E)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hPow := tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr
    have hShift : Tendsto (fun N : ℕ => r ^ (N + 1)) atTop (𝓝 0) := hPow.comp (tendsto_add_atTop_nat 1)
    have hBound : Tendsto (fun N : ℕ => K * r ^ (N + 1)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hShift.const_mul K
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hBound (fun _ => norm_nonneg _) hNorm
  let y := seriesEval (F := F) x f
  have hy : ‖y‖ ≤ c * (K * r) := by
    calc
      ‖y‖ ≤ K * c * r := by
        simpa only [pow_one] using norm_seriesEval_le_of_vanishesBelow hx hr hf hvan
      _ = _ := by ring
  have hSumm : Summable (fun k : ℕ => ((k.factorial : F)⁻¹) • y ^ k) := by
    apply ((summable_geometric_of_lt_one (by positivity : 0 ≤ K * r) hKr).mul_left c).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    rw [norm_smul]
    calc
      _ ≤ ‖((k.factorial : F)⁻¹)‖ * ‖y‖ ^ k := mul_le_mul_of_nonneg_left (norm_pow_le' y hk) (norm_nonneg _)
      _ ≤ ‖((k.factorial : F)⁻¹)‖ * (c * (K * r)) ^ k := by gcongr
      _ = (‖((k.factorial : F)⁻¹)‖ * c ^ k) * (K * r) ^ k := by rw [mul_pow]; ring
      _ ≤ c * (K * r) ^ k := mul_le_mul_of_nonneg_right (hFac k hk) (by positivity)
  have hOther := hSumm.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hCorrespond : (fun N : ℕ => seriesEval (F := F) x (P N)) =
      (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), ((k.factorial : F)⁻¹) • y ^ k) := funext hExplicit
  rw [hCorrespond] at hLim
  rw [congrFun (NormedSpace.exp_eq_tsum F (𝔸 := A)) y]
  exact tendsto_nhds_unique hLim hOther

end Langlands.CyclicWords
