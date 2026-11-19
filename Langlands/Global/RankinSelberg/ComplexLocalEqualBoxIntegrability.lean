import Langlands.Global.RankinSelberg.ComplexLocalEqualTorusBoxes

/-! # Integrability from decay in logarithmic Iwasawa coordinates -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexLocalConvergence

open ArchimedeanLocal Langlands.Archimedean Langlands.QuotientIntegration
open Langlands.RankinSelberg (LeftUnipotentQuotient)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "I" => Fin (r + 1)
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "K" => unitaryCompact ℂ (r + 1)

private theorem tsum_natAbs_pow_lt_top {p : ℝ≥0∞} (hp : p < 1) :
    (∑' m : ℤ, p ^ m.natAbs) < ⊤ := by
  let code (m : ℤ) : Bool × ℕ := (decide (m < 0), m.natAbs)
  have hcode : Function.Injective code := by
    intro m n h
    have h₁ : decide (m < 0) = decide (n < 0) := congrArg Prod.fst h
    have h₂ : m.natAbs = n.natAbs := congrArg Prod.snd h
    by_cases hm : m < 0 <;> by_cases hn : n < 0 <;>
      simp [hm, hn] at h₁ <;> omega
  calc
    (∑' m : ℤ, p ^ m.natAbs) ≤ ∑' i : Bool × ℕ, p ^ i.2 :=
      ENNReal.tsum_comp_le_tsum_of_injective hcode (fun i : Bool × ℕ => p ^ i.2)
    _ = ∑' _ : Bool, ∑' n : ℕ, p ^ n := ENNReal.tsum_prod (f := fun (_ : Bool) (n : ℕ) => p ^ n)
    _ < ⊤ := by
      rw [tsum_fintype]
      exact ENNReal.sum_lt_top.mpr fun _ _ => tsum_geometric_lt_top.mpr hp

private theorem tsum_boxWeights (p : ℝ≥0∞) (n : ℕ) :
    (∑' m : Fin n → ℤ, p ^ (∑ i, (m i).natAbs)) = (∑' z : ℤ, p ^ z.natAbs) ^ n := by
  induction n with
  | zero =>
    let : Unique (Fin 0 → ℤ) := Pi.uniqueOfIsEmpty _
    simp
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)
    rw [← e.tsum_eq, ENNReal.tsum_prod']
    simp only [e, Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      pow_add, ENNReal.tsum_mul_left, ih, ENNReal.tsum_mul_right, pow_succ']

private theorem abs_coord_bound (m : ℤ) (x : ℝ) (hx : (m : ℝ) ≤ x ∧ x ≤ (m : ℝ) + 1) :
    (m.natAbs : ℝ) ≤ |x| + 1 := by
  have hm : (m.natAbs : ℝ) = |(m : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [hm, show (m : ℝ) = x + ((m : ℝ) - x) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonpos (sub_nonpos.mpr hx.1)]
  linarith [hx.2]

private theorem enorm_le_on_box {f : Q → ℂ} {c b : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hf : ∀ (x : I → ℝ) (k : K), ‖f (torusPoint x k)‖ ≤ c * Real.exp (-b * ∑ i, |x i|))
    (m : I → ℤ) {q : Q} (hq : q ∈ torusBox m) :
    ‖f q‖ₑ ≤ ENNReal.ofReal (c * Real.exp (b * (r + 1))) *
      ENNReal.ofReal (Real.exp (-b)) ^ (∑ i, (m i).natAbs) := by
  obtain ⟨⟨x, k⟩, ⟨hx, _⟩, rfl⟩ := hq
  have hcoord : ((∑ i, (m i).natAbs : ℕ) : ℝ) ≤ (∑ i, |x i|) + (r + 1) := by
    push_cast
    calc
      _ ≤ ∑ i, (|x i| + 1) :=
        Finset.sum_le_sum fun i _ => abs_coord_bound (m i) (x i) (hx i (Set.mem_univ i))
      _ = _ := by simp [Finset.sum_add_distrib]
  have hexp : -b * (∑ i, |x i|) ≤ b * (r + 1) + (∑ i, (m i).natAbs : ℕ) * (-b) := by
    nlinarith [mul_le_mul_of_nonneg_left hcoord hb]
  rw [← ofReal_norm]
  refine (ENNReal.ofReal_le_ofReal ((hf x k).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hc))).trans_eq ?_
  rw [Real.exp_add, Real.exp_nat_mul, ENNReal.ofReal_mul hc, ENNReal.ofReal_mul (Real.exp_nonneg _),
    ENNReal.ofReal_pow (Real.exp_nonneg _), ENNReal.ofReal_mul hc]
  ac_rfl

/-- For each compatible quotient measure, sufficiently fast exponential decay in all
logarithmic diagonal coordinates implies absolute integrability. -/
theorem exists_logDecay_threshold (D : ComplexQuotientMeasureData r) :
    ∃ b : ℝ, 0 < b ∧ ∀ {f : Q → ℂ}, AEStronglyMeasurable f D.measure →
      ∀ {c : ℝ}, 0 ≤ c →
        (∀ (x : I → ℝ) (k : K), ‖f (torusPoint x k)‖ ≤ c * Real.exp (-b * ∑ i, |x i|)) →
          Integrable f D.measure := by
  obtain ⟨A, B, hB, hbox⟩ := exists_measure_torusBox_le D
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB'
  let b := Real.log B + 1
  have hb : 0 < b := by dsimp [b]; linarith [Real.log_nonneg hB']
  let p := ENNReal.ofReal (Real.exp (-b))
  have hp : p * (B : ℝ≥0∞) < 1 := by
    have heq : Real.exp (-b) * (B : ℝ) = Real.exp (-1) := by
      calc
        _ = Real.exp (-b) * Real.exp (Real.log B) := by rw [Real.exp_log hBpos]
        _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [b]; ring
    dsimp [p]
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (Real.exp_nonneg _), heq]
    exact ENNReal.ofReal_lt_one.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  refine ⟨b, hb, fun {f} hf {c} hc hdecay => ⟨hf, ?_⟩⟩
  change (∫⁻ q, ‖f q‖ₑ ∂D.measure) < ⊤
  let C := ENNReal.ofReal (c * Real.exp (b * (r + 1)))
  have hl (m : I → ℤ) :
      (∫⁻ q in torusBox m, ‖f q‖ₑ ∂D.measure) ≤
        C * (A : ℝ≥0∞) * (p * (B : ℝ≥0∞)) ^ (∑ i, (m i).natAbs) := by
    let := leftQuotient_t2Space N GeneralLinear.UpperUnipotent.isClosed
    have hm := (isCompact_torusBox m).measurableSet
    calc
      _ ≤ ∫⁻ _ in torusBox m, C * p ^ (∑ i, (m i).natAbs) ∂D.measure :=
        setLIntegral_mono' hm fun _ hq => enorm_le_on_box hc hb.le hdecay m hq
      _ = C * p ^ (∑ i, (m i).natAbs) * D.measure (torusBox m) := by simp
      _ ≤ C * p ^ (∑ i, (m i).natAbs) *
          ((A : ℝ≥0∞) * (B : ℝ≥0∞) ^ (∑ i, (m i).natAbs)) := by gcongr; exact hbox m
      _ = _ := by rw [mul_pow]; ac_rfl
  calc
    (∫⁻ q, ‖f q‖ₑ ∂D.measure) = ∫⁻ q in ⋃ m : I → ℤ, torusBox m, ‖f q‖ₑ ∂D.measure := by
      rw [iUnion_torusBox, Measure.restrict_univ]
    _ ≤ ∑' m : I → ℤ, ∫⁻ q in torusBox m, ‖f q‖ₑ ∂D.measure :=
      lintegral_iUnion_le _ _
    _ ≤ ∑' m : I → ℤ, C * (A : ℝ≥0∞) * (p * (B : ℝ≥0∞)) ^ (∑ i, (m i).natAbs) :=
      ENNReal.tsum_le_tsum hl
    _ < ⊤ := by
      rw [ENNReal.tsum_mul_left, tsum_boxWeights]
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top)
        (ENNReal.pow_lt_top (tsum_natAbs_pow_lt_top hp))

end Langlands.Global.RankinSelbergGlobal.ComplexLocalConvergence
