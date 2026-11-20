import Langlands.Global.RankinSelberg.ArchimedeanInverseMellin
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Exponential type in vertical strips and Gamma factors

See the paired Markdown file.
-/

open MeasureTheory Set Filter Complex
open scoped Topology Real

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanInverseMellin

open ArchimedeanMellinPair

/-- Exponential type in vertical strips: on every strip `a ≤ Re s ≤ b`, the bound
`‖f (x + y i)‖ ≤ C exp (K |y|)` with `C, K ≥ 0`. -/
def StripExpType (f : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ x : ℝ, a ≤ x → x ≤ b → ∀ y : ℝ,
    ‖f (x + y * I)‖ ≤ C * Real.exp (K * |y|)

theorem rpow_le_add {t : ℝ} (ht : 0 < t) {a b x : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    t ^ x ≤ t ^ a + t ^ b := by
  have ha := (Real.rpow_pos_of_pos ht a).le
  have hb := (Real.rpow_pos_of_pos ht b).le
  rcases le_total t 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge ht h hax
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h hxb
    linarith

namespace StripExpType

theorem congr {f g : ℂ → ℂ} (hf : StripExpType f) (h : ∀ s, f s = g s) : StripExpType g := by
  have : f = g := funext h
  rwa [← this]

theorem mul {f g : ℂ → ℂ} (hf : StripExpType f) (hg : StripExpType g) :
    StripExpType (fun s => f s * g s) := by
  intro a b
  obtain ⟨C₁, K₁, hC₁, hK₁, h₁⟩ := hf a b
  obtain ⟨C₂, K₂, hC₂, hK₂, h₂⟩ := hg a b
  refine ⟨C₁ * C₂, K₁ + K₂, mul_nonneg hC₁ hC₂, add_nonneg hK₁ hK₂, fun x hax hxb y => ?_⟩
  rw [norm_mul]
  calc ‖f (x + y * I)‖ * ‖g (x + y * I)‖
      ≤ (C₁ * Real.exp (K₁ * |y|)) * (C₂ * Real.exp (K₂ * |y|)) :=
        mul_le_mul (h₁ x hax hxb y) (h₂ x hax hxb y) (norm_nonneg _) (by positivity)
    _ = C₁ * C₂ * Real.exp ((K₁ + K₂) * |y|) := by rw [add_mul, Real.exp_add]; ring

theorem const (c : ℂ) : StripExpType (fun _ => c) :=
  fun _ _ => ⟨‖c‖, 0, norm_nonneg _, le_rfl, fun x _ _ y => by simp⟩

theorem comp_add {f : ℂ → ℂ} (hf : StripExpType f) (w : ℂ) :
    StripExpType (fun s => f (s + w)) := by
  intro a b
  obtain ⟨C, K, hC, hK, h⟩ := hf (a + w.re) (b + w.re)
  refine ⟨C * Real.exp (K * |w.im|), K, by positivity, hK, fun x hax hxb y => ?_⟩
  have hs : (x : ℂ) + y * I + w = ((x + w.re : ℝ) : ℂ) + ((y + w.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  simp only
  rw [hs]
  refine (h _ (by linarith) (by linarith) _).trans ?_
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC
  have := abs_add_le y w.im
  nlinarith

theorem comp_ofReal_mul {f : ℂ → ℂ} (hf : StripExpType f) (r : ℝ) :
    StripExpType (fun s => f (r * s)) := by
  intro a b
  set R := |r| * (|a| + |b|) with hR
  obtain ⟨C, K, hC, hK, h⟩ := hf (-R) R
  refine ⟨C, K * |r|, hC, by positivity, fun x hax hxb y => ?_⟩
  have hs : (r : ℂ) * (x + y * I) = ((r * x : ℝ) : ℂ) + ((r * y : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hx : |x| ≤ |a| + |b| := by
    rw [abs_le]
    constructor
    · have := neg_abs_le a
      have := abs_nonneg b
      linarith
    · have := le_abs_self b
      have := abs_nonneg a
      linarith
  have hrx : |r * x| ≤ R := by
    rw [abs_mul, hR]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg r)
  simp only
  rw [hs]
  refine (h _ (abs_le.1 hrx).1 (abs_le.1 hrx).2 _).trans (le_of_eq ?_)
  rw [abs_mul]
  ring_nf

theorem ofReal_cpow {r : ℝ} (hr : 0 < r) : StripExpType (fun s => (r : ℂ) ^ s) := by
  intro a b
  refine ⟨r ^ a + r ^ b, 0, by positivity, le_rfl, fun x hax hxb y => ?_⟩
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, zero_mul, Real.exp_zero]
  exact rpow_le_add hr hax hxb

theorem list_prod {ι : Type*} (l : List ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ l, StripExpType (f i)) :
    StripExpType (fun s => (l.map fun i => f i s).prod) := by
  induction l with
  | nil => simpa using const 1
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hf i List.mem_cons_self).mul (ih fun j hj => hf j (List.mem_cons_of_mem i hj))

end StripExpType

/-- A continuous function is bounded on each rectangle `a ≤ Re s ≤ b`, `|Im s| ≤ 1`. -/
theorem bounded_on_rect {f : ℂ → ℂ} (hf : Continuous f) (a b : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, a ≤ x → x ≤ b → ∀ y : ℝ, |y| ≤ 1 → ‖f (x + y * I)‖ ≤ B := by
  have hK : IsCompact (Icc a b ×ˢ Icc (-1 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hc : Continuous (fun p : ℝ × ℝ => f (p.1 + p.2 * I)) := hf.comp (by fun_prop)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x hax hxb y hy => ?_⟩
  exact (hB (x, y) ⟨⟨hax, hxb⟩, abs_le.1 hy⟩).trans (le_max_left _ _)

theorem norm_sin_le (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have h := Complex.two_sin z
  have h2 : ‖(2 : ℂ) * Complex.sin z‖ ≤ Real.exp z.im + Real.exp (-z.im) := by
    rw [h, norm_mul, Complex.norm_I, mul_one]
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [Complex.norm_exp, Complex.norm_exp]
    simp
  rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by simp] at h2
  have h3 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.2 (le_abs_self _)
  have h4 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.2 (neg_le_abs _)
  linarith

/-- `‖Γ(z)‖ ≤ Γ(p) + Γ(q)` for `0 < p ≤ Re z ≤ q`. -/
theorem norm_Gamma_le {p q : ℝ} (hp : 0 < p) {z : ℂ} (hpz : p ≤ z.re) (hzq : z.re ≤ q) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma p + Real.Gamma q := by
  have hz : 0 < z.re := lt_of_lt_of_le hp hpz
  have hq : 0 < q := lt_of_lt_of_le hz hzq
  have hip := Real.GammaIntegral_convergent hp
  have hiq := Real.GammaIntegral_convergent hq
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral, Real.Gamma_eq_integral hp,
    Real.Gamma_eq_integral hq, ← integral_add hip hiq]
  refine norm_integral_le_of_norm_le (hip.add hiq) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simp only [Complex.sub_re, Complex.one_re]
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (rpow_le_add ht (by linarith) (by linarith))
    (Real.exp_pos _).le

/-- The reflection formula in the form `Γ(s)⁻¹ = Γ(1 - s) sin(π s) / π`, for `Re s < 1`. -/
theorem inv_Gamma_eq_of_re_lt_one {s : ℂ} (hs : s.re < 1) :
    (Complex.Gamma s)⁻¹ = Complex.Gamma (1 - s) * Complex.sin (π * s) / π := by
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  by_cases hsin : Complex.sin (π * s) = 0
  · obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.1 hsin
    have hsk : s = k := by
      have : s * π = (k : ℂ) * π := by rw [mul_comm]; exact hk
      exact mul_right_cancel₀ hpi this
    have hk0 : k ≤ 0 := by
      have hre : s.re = k := by rw [hsk]; simp
      by_contra hk
      have hk' : 0 < k := not_le.1 hk
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk'
      linarith
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨k.natAbs, by omega⟩
    rw [hsin, mul_zero, zero_div, hsk, hn]
    push_cast
    rw [Complex.Gamma_neg_nat_eq_zero, inv_zero]
  · have h := Complex.Gamma_mul_Gamma_one_sub s
    have hG : Complex.Gamma s ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h
      exact (div_ne_zero hpi hsin) h.symm
    have h' : Complex.Gamma s * Complex.Gamma (1 - s) * Complex.sin (π * s) = π := by
      rw [h, div_mul_cancel₀ _ hsin]
    rw [eq_div_iff hpi]
    calc (Complex.Gamma s)⁻¹ * π
        = (Complex.Gamma s)⁻¹ *
          (Complex.Gamma s * Complex.Gamma (1 - s) * Complex.sin (π * s)) := by rw [h']
      _ = _ := by field_simp

theorem inv_Gamma_bound_left {a b : ℝ} (hb : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, a ≤ x → x ≤ b → ∀ y : ℝ,
      ‖(Complex.Gamma (x + y * I))⁻¹‖ ≤ C * Real.exp (π * |y|) := by
  refine ⟨(|Real.Gamma (1 - b)| + |Real.Gamma (1 - a)|) / π, by positivity,
    fun x hax hxb y => ?_⟩
  have hre : ((x : ℂ) + y * I).re < 1 := by simp; linarith
  rw [inv_Gamma_eq_of_re_lt_one hre, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  have hG : ‖Complex.Gamma (1 - ((x : ℂ) + y * I))‖ ≤
      |Real.Gamma (1 - b)| + |Real.Gamma (1 - a)| := by
    refine (norm_Gamma_le (p := 1 - b) (q := 1 - a) (by linarith) ?_ ?_).trans ?_
    · simp; linarith
    · simp; linarith
    · exact add_le_add (le_abs_self _) (le_abs_self _)
  have hS : ‖Complex.sin (π * ((x : ℂ) + y * I))‖ ≤ Real.exp (π * |y|) := by
    refine (norm_sin_le _).trans (le_of_eq ?_)
    congr 1
    simp [abs_mul, abs_of_pos Real.pi_pos]
  rw [div_le_iff₀ Real.pi_pos]
  calc ‖Complex.Gamma (1 - ((x : ℂ) + y * I))‖ * ‖Complex.sin (π * ((x : ℂ) + y * I))‖
      ≤ (|Real.Gamma (1 - b)| + |Real.Gamma (1 - a)|) * Real.exp (π * |y|) :=
        mul_le_mul hG hS (norm_nonneg _) (by positivity)
    _ = _ := by field_simp

theorem inv_Gamma_bound_shift {a b C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x : ℝ, a ≤ x → x ≤ b → ∀ y : ℝ,
      ‖(Complex.Gamma (x + y * I))⁻¹‖ ≤ C * Real.exp (π * |y|)) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ x : ℝ, a + 1 ≤ x → x ≤ b + 1 → ∀ y : ℝ,
      ‖(Complex.Gamma (x + y * I))⁻¹‖ ≤ C' * Real.exp (π * |y|) := by
  obtain ⟨B, hB0, hB⟩ := bounded_on_rect
    (f := fun s => (Complex.Gamma s)⁻¹) Complex.differentiable_one_div_Gamma.continuous
    (a + 1) (b + 1)
  refine ⟨max C B, le_max_of_le_left hC0, fun x hax hxb y => ?_⟩
  have hexp : 1 ≤ Real.exp (π * |y|) := Real.one_le_exp (by positivity)
  rcases le_total |y| 1 with hy | hy
  · calc ‖(Complex.Gamma (x + y * I))⁻¹‖ ≤ B := hB x hax hxb y hy
      _ ≤ max C B * 1 := by rw [mul_one]; exact le_max_right _ _
      _ ≤ max C B * Real.exp (π * |y|) :=
          mul_le_mul_of_nonneg_left hexp (le_max_of_le_left hC0)
  · have hne : (x : ℂ) + y * I - 1 ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      rw [this, abs_zero] at hy
      linarith
    have hrec : Complex.Gamma (x + y * I) =
        ((x : ℂ) + y * I - 1) * Complex.Gamma ((x : ℂ) + y * I - 1) := by
      have := Complex.Gamma_add_one _ hne
      rwa [sub_add_cancel] at this
    have hs1 : (x : ℂ) + y * I - 1 = ((x - 1 : ℝ) : ℂ) + y * I := by push_cast; ring
    have hnorm : ‖((x : ℂ) + y * I - 1)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      apply inv_le_one_of_one_le₀
      calc (1 : ℝ) ≤ |y| := hy
        _ = |((x : ℂ) + y * I - 1).im| := by simp
        _ ≤ ‖(x : ℂ) + y * I - 1‖ := Complex.abs_im_le_norm _
    have := hC (x - 1) (by linarith) (by linarith) y
    rw [← hs1] at this
    rw [hrec, mul_inv, norm_mul]
    calc ‖((x : ℂ) + y * I - 1)⁻¹‖ * ‖(Complex.Gamma ((x : ℂ) + y * I - 1))⁻¹‖
        ≤ 1 * (C * Real.exp (π * |y|)) := mul_le_mul hnorm this (norm_nonneg _) zero_le_one
      _ ≤ max C B * Real.exp (π * |y|) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-- `1 / Γ` has exponential type `π` in vertical strips. -/
theorem inv_Gamma_stripExpType : StripExpType (fun s => (Complex.Gamma s)⁻¹) := by
  have key : ∀ n : ℕ, ∀ a b : ℝ, b < 1 + n → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, a ≤ x → x ≤ b →
      ∀ y : ℝ, ‖(Complex.Gamma (x + y * I))⁻¹‖ ≤ C * Real.exp (π * |y|) := by
    intro n
    induction n with
    | zero => intro a b hb; exact inv_Gamma_bound_left (by simpa using hb)
    | succ n ih =>
      intro a b hb
      obtain ⟨C, hC0, hC⟩ := ih (a - 1) (b - 1) (by push_cast at hb; linarith)
      obtain ⟨C', hC'0, hC'⟩ := inv_Gamma_bound_shift hC0 hC
      exact ⟨C', hC'0, fun x hax hxb y => hC' x (by linarith) (by linarith) y⟩
  intro a b
  obtain ⟨n, hn⟩ := exists_nat_gt b
  obtain ⟨C, hC0, hC⟩ := key n a b (by linarith)
  exact ⟨C, π, hC0, Real.pi_pos.le, hC⟩

/-- `1 / Γ_ℝ` has exponential type in vertical strips. -/
theorem inv_Gammaℝ_stripExpType : StripExpType (fun s => (Complex.Gammaℝ s)⁻¹) := by
  have h1 : StripExpType (fun s => (π : ℂ) ^ (((1 / 2 : ℝ) : ℂ) * s)) :=
    (StripExpType.ofReal_cpow Real.pi_pos).comp_ofReal_mul (1 / 2)
  have h2 : StripExpType (fun s => (Complex.Gamma (((1 / 2 : ℝ) : ℂ) * s))⁻¹) :=
    inv_Gamma_stripExpType.comp_ofReal_mul (1 / 2)
  refine (h1.mul h2).congr fun s => ?_
  have hs : ((1 / 2 : ℝ) : ℂ) * s = s / 2 := by push_cast; ring
  rw [hs, Complex.Gammaℝ_def, mul_inv, neg_div, Complex.cpow_neg, inv_inv]

/-- `1 / Γ_ℂ` has exponential type in vertical strips. -/
theorem inv_Gammaℂ_stripExpType : StripExpType (fun s => (Complex.Gammaℂ s)⁻¹) := by
  have h1 : StripExpType (fun s => ((2 * π : ℝ) : ℂ) ^ s) :=
    StripExpType.ofReal_cpow (by positivity)
  refine ((StripExpType.const (2⁻¹ : ℂ)).mul (h1.mul inv_Gamma_stripExpType)).congr
    fun s => ?_
  rw [Complex.Gammaℂ_def, mul_inv, mul_inv, Complex.cpow_neg, inv_inv]
  push_cast
  ring

/-- Multiplying a function of exponential type by `exp (s ^ 2)` gives strip decay. -/
theorem stripDecay_exp_sq_mul {f : ℂ → ℂ} (hf : StripExpType f) :
    StripDecay (fun s => Complex.exp (s ^ 2) * f s) := by
  intro a b
  obtain ⟨C, K, hC, hK, h⟩ := hf a b
  refine ⟨2 * C * Real.exp (a ^ 2 + b ^ 2 + K ^ 2 / 2), fun x hax hxb y => ?_⟩
  rw [norm_mul, Complex.norm_exp]
  have hre : (((x : ℂ) + y * I) ^ 2).re = x ^ 2 - y ^ 2 := by
    simp [sq]
  rw [hre]
  have hx2 : x ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases le_total 0 x with h0 | h0
    · nlinarith
    · nlinarith
  have hKy : K * |y| ≤ y ^ 2 / 2 + K ^ 2 / 2 := by
    nlinarith [sq_nonneg (|y| - K), sq_abs y]
  have hq : 1 + y ^ 2 ≤ 2 * Real.exp (y ^ 2 / 2) := by
    have := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ y ^ 2 / 2)
    nlinarith [sq_nonneg y]
  have hpos : 0 < 1 + y ^ 2 := by positivity
  calc Real.exp (x ^ 2 - y ^ 2) * ‖f (x + y * I)‖
      ≤ Real.exp (x ^ 2 - y ^ 2) * (C * Real.exp (K * |y|)) :=
        mul_le_mul_of_nonneg_left (h x hax hxb y) (Real.exp_pos _).le
    _ = C * Real.exp (x ^ 2 - y ^ 2 + K * |y|) := by rw [Real.exp_add]; ring
    _ ≤ C * Real.exp (a ^ 2 + b ^ 2 + K ^ 2 / 2 - y ^ 2 / 2) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC
        linarith
    _ = C * Real.exp (a ^ 2 + b ^ 2 + K ^ 2 / 2) * (Real.exp (y ^ 2 / 2))⁻¹ := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg]; ring
    _ ≤ C * Real.exp (a ^ 2 + b ^ 2 + K ^ 2 / 2) * (2 * (1 + y ^ 2)⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [inv_le_comm₀ (Real.exp_pos _) (by positivity), mul_inv, inv_inv]
        nlinarith [Real.exp_pos (y ^ 2 / 2)]
    _ = 2 * C * Real.exp (a ^ 2 + b ^ 2 + K ^ 2 / 2) * (1 + y ^ 2)⁻¹ := by ring

theorem StripDecay.comp_add_ofReal {f : ℂ → ℂ} (hf : StripDecay f) (c : ℝ) :
    StripDecay (fun s => f (s + c)) := by
  intro a b
  obtain ⟨C, hC⟩ := hf (a + c) (b + c)
  refine ⟨C, fun x hax hxb y => ?_⟩
  have hs : (x : ℂ) + y * I + c = ((x + c : ℝ) : ℂ) + y * I := by push_cast; ring
  simp only
  rw [hs]
  exact hC _ (by linarith) (by linarith) y

theorem StripDecay.congr {f g : ℂ → ℂ} (hf : StripDecay f) (h : ∀ s, f s = g s) :
    StripDecay g := by
  have : f = g := funext h
  rwa [← this]

end Langlands.Global.RankinSelbergGlobal.ArchimedeanInverseMellin
