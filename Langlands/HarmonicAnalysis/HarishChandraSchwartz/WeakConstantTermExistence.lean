import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeakConstantTermUniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Existence of the weak constant term (Waldspurger, Lemma III.5.1)

Waldspurger, Lemma III.5.1 (printed pp. 269–270): for `f ∈ A^w(G)` there is a unique
`f^w_P ∈ A^w(M)` with `lim_{a →_P ∞} [δ_P(ma)^{-1/2} f(ma) - f^w_P(ma)] = 0` for every `m ∈ M`.
The existence part of the proof writes `ϕ(a) = f_P(ma) - f^w_P(ma)` in the form
`ϕ(a) = ∑_{χ ∈ E} Q_χ(H_M(a)) χ(a)` with `Re(χ) ∈ +ā_P^{G*}` and `Re(χ) ≠ 0` (condition (1) of the
proof) and asserts that these conditions give `lim_{a →_P ∞} ϕ(a) = 0`.

This module proves that assertion under one additional hypothesis: the polynomials `Q_χ` are
polynomials in linear coordinates `ℓ_i` lying in the span of `Σ(P)`
(`tendstoZeroAlongParabolic_exponentialPolynomial`). The condition `Re(χ) ∈ +ā_P^{G*}`,
`Re(χ) ≠ 0` is `IsDecayingAlongParabolic`: `|χ(a)| ≤ exp(-⟨λ, H_M(a)⟩)` for a combination
`λ = ∑_{α ∈ Σ(P)} x_α α` with `x_α ≥ 0` and some `x_α > 0`. Without the span hypothesis the
assertion fails, since the conditions (i), (ii) of III.5 do not constrain the components of
`H_M(a)` on which the `α ∈ Σ(P)` vanish: `not_tendstoZeroAlongParabolic_fst_mul_expNegSnd` is an
example with `A = ℝ²`, `Σ(P) = {a ↦ a₂}` and `ϕ(a) = a₁ e^{-a₂}`.

The existence argument itself (`tendstoZeroAlongParabolic_sub_of_eventually_eq`) combines this
limit with the identity `δ_P(ma)^{-1/2} f(ma) = f_P(ma)` for `a` deep in the chamber, and
`existsUnique_tendstoZeroAlongParabolic_sub` combines it with the uniqueness part of
`WeakConstantTermUniqueness`.
-/

noncomputable section

open Filter Topology Asymptotics

namespace Langlands.HarishChandraSchwartz

section Bounds

variable {ι E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A complex polynomial is bounded by `C M^d` on the points whose coordinates in a finite set
`s` (containing its variables) have norm at most `M ≥ 1`. -/
theorem exists_norm_eval_le (p : MvPolynomial ι ℂ) :
    ∃ (s : Finset ι) (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ (x : ι → ℂ) (M : ℝ), 1 ≤ M →
      (∀ i ∈ s, ‖x i‖ ≤ M) → ‖MvPolynomial.eval x p‖ ≤ C * M ^ d := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨∅, ‖c‖, 0, norm_nonneg c, fun x M _ _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨s₁, C₁, d₁, hC₁, h₁⟩ := hp
    obtain ⟨s₂, C₂, d₂, hC₂, h₂⟩ := hq
    refine ⟨s₁ ∪ s₂, C₁ + C₂, max d₁ d₂, add_nonneg hC₁ hC₂, fun x M hM hx => ?_⟩
    have e₁ := h₁ x M hM fun i hi => hx i (Finset.mem_union_left _ hi)
    have e₂ := h₂ x M hM fun i hi => hx i (Finset.mem_union_right _ hi)
    have p₁ : M ^ d₁ ≤ M ^ max d₁ d₂ := pow_le_pow_right₀ hM (le_max_left _ _)
    have p₂ : M ^ d₂ ≤ M ^ max d₁ d₂ := pow_le_pow_right₀ hM (le_max_right _ _)
    calc ‖MvPolynomial.eval x (p + q)‖
        ≤ ‖MvPolynomial.eval x p‖ + ‖MvPolynomial.eval x q‖ := by
          rw [map_add]; exact norm_add_le _ _
      _ ≤ C₁ * M ^ d₁ + C₂ * M ^ d₂ := add_le_add e₁ e₂
      _ ≤ C₁ * M ^ max d₁ d₂ + C₂ * M ^ max d₁ d₂ :=
          add_le_add (mul_le_mul_of_nonneg_left p₁ hC₁) (mul_le_mul_of_nonneg_left p₂ hC₂)
      _ = (C₁ + C₂) * M ^ max d₁ d₂ := by ring
  | mul_X p i hp =>
    obtain ⟨s, C, d, hC, h⟩ := hp
    refine ⟨insert i s, C, d + 1, hC, fun x M hM hx => ?_⟩
    have e := h x M hM fun k hk => hx k (Finset.mem_insert_of_mem hk)
    have ei := hx i (Finset.mem_insert_self i s)
    rw [map_mul, MvPolynomial.eval_X, norm_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul e ei (norm_nonneg _) (mul_nonneg hC (pow_nonneg (by linarith) d))

/-- A linear form in the span of a finite set `S` of linear forms is bounded by `C T` at every
point where all `α ∈ S` are bounded by `T` in absolute value. -/
theorem exists_abs_apply_le_of_mem_span {S : Finset (Module.Dual ℝ E)} {ℓ : Module.Dual ℝ E}
    (hℓ : ℓ ∈ Submodule.span ℝ (S : Set (Module.Dual ℝ E))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ) (H : E), (∀ α ∈ S, |α H| ≤ T) → |ℓ H| ≤ C * T := by
  induction hℓ using Submodule.span_induction with
  | mem α hα => exact ⟨1, zero_le_one, fun T H h => by rw [one_mul]; exact h α hα⟩
  | zero => exact ⟨0, le_rfl, fun T H _ => by simp⟩
  | add ℓ₁ ℓ₂ _ _ h₁ h₂ =>
    obtain ⟨C₁, hC₁, e₁⟩ := h₁
    obtain ⟨C₂, hC₂, e₂⟩ := h₂
    refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun T H h => ?_⟩
    rw [LinearMap.add_apply, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (e₁ T H h) (e₂ T H h))
  | smul r ℓ _ h =>
    obtain ⟨C, hC, e⟩ := h
    refine ⟨|r| * C, mul_nonneg (abs_nonneg r) hC, fun T H h => ?_⟩
    rw [LinearMap.smul_apply, smul_eq_mul, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (e T H h) (abs_nonneg r)

/-- `D (1 + K t)^d e^{-c t}` is eventually smaller than any `ε > 0` as `t → ∞`, for `c > 0` and
`K ≥ 0`. -/
theorem eventually_mul_pow_mul_exp_neg_lt {c : ℝ} (hc : 0 < c) {K : ℝ} (hK : 0 ≤ K) (D : ℝ)
    (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, D * (1 + K * t) ^ d * Real.exp (-(c * t)) < ε := by
  have h := (isLittleO_pow_exp_pos_mul_atTop d hc).tendsto_div_nhds_zero
  have h₂ : Tendsto (fun t : ℝ => |D| * (1 + K) ^ d * (t ^ d / Real.exp (c * t))) atTop
      (𝓝 0) := by
    simpa using h.const_mul (|D| * (1 + K) ^ d)
  filter_upwards [h₂.eventually (gt_mem_nhds hε), eventually_ge_atTop 1] with t ht ht1
  refine lt_of_le_of_lt ?_ ht
  have hlin : 0 ≤ 1 + K * t := by nlinarith
  have hle : (1 + K * t) ^ d ≤ (1 + K) ^ d * t ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hlin (by nlinarith) d
  rw [Real.exp_neg, ← div_eq_mul_inv, mul_div_assoc]
  calc D * ((1 + K * t) ^ d / Real.exp (c * t))
      ≤ |D| * ((1 + K * t) ^ d / Real.exp (c * t)) :=
        mul_le_mul_of_nonneg_right (le_abs_self D)
          (div_nonneg (pow_nonneg hlin d) (Real.exp_pos _).le)
    _ ≤ |D| * ((1 + K) ^ d * t ^ d / Real.exp (c * t)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hle (Real.exp_pos _).le)
          (abs_nonneg D)
    _ = |D| * (1 + K) ^ d * (t ^ d / Real.exp (c * t)) := by ring

end Bounds

section ParabolicLimit

variable {A E : Type*} [AddCommGroup E] [Module ℝ E]

/-- If `f = g` at every `a` with `⟨α, H_M(a)⟩ > R₀` for all `α ∈ S`, and
`lim_{a →_P ∞} g(a) = 0`, then `lim_{a →_P ∞} f(a) = 0`. -/
theorem TendstoZeroAlongParabolic.congr_of_forall {HM : A → E}
    {S : Finset (Module.Dual ℝ E)} {f g : A → ℂ} (hg : TendstoZeroAlongParabolic HM S g)
    {R₀ : ℝ} (hfg : ∀ a, (∀ α ∈ S, R₀ < α (HM a)) → f a = g a) :
    TendstoZeroAlongParabolic HM S f := by
  intro ε hε η hη
  obtain ⟨R, hR, h⟩ := hg ε hε η hη
  refine ⟨max R R₀, lt_max_of_lt_left hR, fun a hi hii => ?_⟩
  rw [hfg a fun α hα => (le_max_right _ _).trans_lt (hi α hα)]
  exact h a (fun α hα => (le_max_left _ _).trans_lt (hi α hα)) hii

variable [CommGroup A]

/-- Condition (1) in the proof of Waldspurger, Lemma III.5.1 (printed p. 270): `Re(χ) ∈ +ā_P^{G*}`
and `Re(χ) ≠ 0`, in the form `|χ(a)| ≤ exp(-⟨λ, H_M(a)⟩)` for a combination
`λ = ∑_{α ∈ S} x_α α` of the forms in `S` (in place of `Σ(P)`) with `x_α ≥ 0` for all `α ∈ S`
and `x_α > 0` for some `α ∈ S`. -/
def IsDecayingAlongParabolic (HM : A → E) (S : Finset (Module.Dual ℝ E)) (χ : A →* ℂˣ) :
    Prop :=
  ∃ x : Module.Dual ℝ E → ℝ, (∀ α ∈ S, 0 ≤ x α) ∧ (∃ α ∈ S, 0 < x α) ∧
    ∀ a, ‖(χ a : ℂ)‖ ≤ Real.exp (-∑ α ∈ S, x α * α (HM a))

variable {ι κ : Type*} [Fintype κ]

/-- The limit assertion in the existence part of Waldspurger, Lemma III.5.1 (printed p. 270),
with polynomials in coordinates from the span of `S`: if
`ϕ(a) = ∑_j χ_j(a) Q_j(H_M(a))` with every `χ_j` satisfying `IsDecayingAlongParabolic` and the
`Q_j` polynomials in linear forms `ℓ_i` in the span of `S`, then `lim_{a →_P ∞} ϕ(a) = 0`. -/
theorem tendstoZeroAlongParabolic_exponentialPolynomial {HM : A → E}
    {S : Finset (Module.Dual ℝ E)} {ℓ : ι → Module.Dual ℝ E}
    (hℓ : ∀ i, ℓ i ∈ Submodule.span ℝ (S : Set (Module.Dual ℝ E))) {χ : κ → A →* ℂˣ}
    (hχ : ∀ j, IsDecayingAlongParabolic HM S (χ j)) (Q : κ → MvPolynomial ι ℂ) :
    TendstoZeroAlongParabolic HM S (exponentialPolynomial HM ℓ χ Q) := by
  classical
  intro ε hε η hη
  choose x hx0 hxpos hχb using hχ
  choose α₁ hα₁S hα₁ using hxpos
  choose Cℓ hCℓ0 hCℓ using fun i => exists_abs_apply_le_of_mem_span (hℓ i)
  choose s D d hD0 hD using fun j => exists_norm_eval_le (Q j)
  rcases S.eq_empty_or_nonempty with hS | ⟨α₀, hα₀⟩
  · -- without forms in `S` there are no decaying characters
    have : IsEmpty κ := ⟨fun j => by simpa [hS] using hα₁S j⟩
    exact ⟨1, one_pos, fun a _ _ => by simp [exponentialPolynomial, hε]⟩
  set K : κ → ℝ := fun j => (∑ i ∈ s j, Cℓ i) / η with hK
  have hK0 : ∀ j, 0 ≤ K j := fun j =>
    div_nonneg (Finset.sum_nonneg fun i _ => hCℓ0 i) hη.le
  set ε' : ℝ := ε / (Fintype.card κ + 1) with hε'
  have hε'0 : 0 < ε' := div_pos hε (by positivity)
  have hev : ∀ᶠ t : ℝ in atTop, ∀ j, D j * (1 + K j * t) ^ d j *
      Real.exp (-((x j (α₁ j) * η) * t)) < ε' :=
    eventually_all.2 fun j =>
      eventually_mul_pow_mul_exp_neg_lt (mul_pos (hα₁ j) hη) (hK0 j) (D j) (d j) hε'0
  obtain ⟨T, hT⟩ := eventually_atTop.1 hev
  refine ⟨max T 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun a hi hii => ?_⟩
  have ht : max T 1 < α₀ (HM a) := hi α₀ hα₀
  have ht0 : 0 < α₀ (HM a) := lt_of_lt_of_le one_pos (le_max_right T 1) |>.trans ht
  have hpos : ∀ β ∈ S, 0 < β (HM a) := fun β hβ =>
    (lt_of_lt_of_le one_pos (le_max_right T 1)).trans (hi β hβ)
  -- every `β ∈ S` is at most `⟨α₀, H_M(a)⟩ / η`, by (ii)
  have hle : ∀ β ∈ S, |β (HM a)| ≤ α₀ (HM a) / η := fun β hβ => by
    rw [abs_of_pos (hpos β hβ), le_div_iff₀ hη]
    have := hii α₀ hα₀ β hβ
    linarith
  have hterm : ∀ j, ‖(χ j a : ℂ) *
      MvPolynomial.eval (fun i => ((ℓ i (HM a) : ℝ) : ℂ)) (Q j)‖ < ε' := by
    intro j
    have hKt : 0 ≤ K j * α₀ (HM a) := mul_nonneg (hK0 j) ht0.le
    have hM1 : 1 ≤ 1 + K j * α₀ (HM a) := by linarith
    have hx : ∀ i ∈ s j, ‖((ℓ i (HM a) : ℝ) : ℂ)‖ ≤ 1 + K j * α₀ (HM a) := by
      intro i hi
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h₂ : Cℓ i ≤ ∑ i ∈ s j, Cℓ i :=
        Finset.single_le_sum (f := Cℓ) (fun i _ => hCℓ0 i) hi
      calc |ℓ i (HM a)| ≤ Cℓ i * (α₀ (HM a) / η) := hCℓ i _ (HM a) hle
        _ ≤ (∑ i ∈ s j, Cℓ i) * (α₀ (HM a) / η) :=
            mul_le_mul_of_nonneg_right h₂ (div_nonneg ht0.le hη.le)
        _ = K j * α₀ (HM a) := by rw [hK]; ring
        _ ≤ 1 + K j * α₀ (HM a) := by linarith
    have hQ := hD j _ _ hM1 hx
    -- `|χ_j(a)| ≤ exp(-x_j η ⟨α₀, H_M(a)⟩)`, since `⟨α₁, H_M(a)⟩ > η ⟨α₀, H_M(a)⟩` by (ii)
    have hχj : ‖(χ j a : ℂ)‖ ≤ Real.exp (-((x j (α₁ j) * η) * α₀ (HM a))) := by
      refine (hχb j a).trans (Real.exp_le_exp.2 (neg_le_neg ?_))
      have h₁ : x j (α₁ j) * α₁ j (HM a) ≤ ∑ α ∈ S, x j α * α (HM a) :=
        Finset.single_le_sum (f := fun α => x j α * α (HM a))
          (fun α hα => mul_nonneg (hx0 j α hα) (hpos α hα).le) (hα₁S j)
      have h₂ : η * α₀ (HM a) < α₁ j (HM a) := hii (α₁ j) (hα₁S j) α₀ hα₀
      have h₃ : x j (α₁ j) * (η * α₀ (HM a)) ≤ x j (α₁ j) * α₁ j (HM a) :=
        mul_le_mul_of_nonneg_left h₂.le (hα₁ j).le
      linarith
    calc ‖(χ j a : ℂ) * MvPolynomial.eval (fun i => ((ℓ i (HM a) : ℝ) : ℂ)) (Q j)‖
        = ‖(χ j a : ℂ)‖ * ‖MvPolynomial.eval (fun i => ((ℓ i (HM a) : ℝ) : ℂ)) (Q j)‖ :=
          norm_mul _ _
      _ ≤ Real.exp (-((x j (α₁ j) * η) * α₀ (HM a))) *
          (D j * (1 + K j * α₀ (HM a)) ^ d j) :=
          mul_le_mul hχj hQ (norm_nonneg _) (Real.exp_pos _).le
      _ = D j * (1 + K j * α₀ (HM a)) ^ d j *
          Real.exp (-((x j (α₁ j) * η) * α₀ (HM a))) := by ring
      _ < ε' := hT _ ((le_max_left T 1).trans ht.le) j
  calc ‖exponentialPolynomial HM ℓ χ Q a‖
      ≤ ∑ j, ‖(χ j a : ℂ) * MvPolynomial.eval (fun i => ((ℓ i (HM a) : ℝ) : ℂ)) (Q j)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j : κ, ε' := Finset.sum_le_sum fun j _ => (hterm j).le
    _ = Fintype.card κ * ε' := by simp
    _ < (Fintype.card κ + 1) * ε' := by nlinarith
    _ = ε := by rw [hε']; field_simp

/-- The existence argument of Waldspurger, Lemma III.5.1 (printed p. 270), for functions on a
monoid `M` containing `A` through `j`: if for every `m` the function `F` (in the source
`F(g) = δ_P(g)^{-1/2} f(g)`) agrees with `f_P` on `m A` deep in the chamber, and
`a ↦ f_P(m a) - f^w(m a)` has the form (1) with characters satisfying
`IsDecayingAlongParabolic` and polynomials in coordinates from the span of `S`, then
`lim_{a →_P ∞} [F(m a) - f^w(m a)] = 0` for every `m`. -/
theorem tendstoZeroAlongParabolic_sub_of_eventually_eq {M : Type*} [Monoid M] (j : A →* M)
    {HM : A → E} {S : Finset (Module.Dual ℝ E)} {ℓ : ι → Module.Dual ℝ E}
    (hℓ : ∀ i, ℓ i ∈ Submodule.span ℝ (S : Set (Module.Dual ℝ E))) {F fP fw : M → ℂ}
    (hasym : ∀ m, ∃ R : ℝ, ∀ a, (∀ α ∈ S, R < α (HM a)) → F (m * j a) = fP (m * j a))
    (hdec : ∀ m, ∃ (n : ℕ) (χ : Fin n → A →* ℂˣ) (Q : Fin n → MvPolynomial ι ℂ),
      (∀ i, IsDecayingAlongParabolic HM S (χ i)) ∧
        ∀ a, fP (m * j a) - fw (m * j a) = exponentialPolynomial HM ℓ χ Q a) (m : M) :
    TendstoZeroAlongParabolic HM S (fun a => F (m * j a) - fw (m * j a)) := by
  obtain ⟨R, hR⟩ := hasym m
  obtain ⟨n, χ, Q, hχ, hφ⟩ := hdec m
  refine (tendstoZeroAlongParabolic_exponentialPolynomial hℓ hχ Q).congr_of_forall
    (R₀ := R) fun a ha => ?_
  rw [hR a ha, hφ a]

/-- Waldspurger, Lemma III.5.1 (printed pp. 269–270), abstract form: under the hypotheses of
`tendstoZeroAlongParabolic_sub_of_eventually_eq` for an `f^w` in a class `C` of functions whose
pairwise differences on every `m A` have the form (1) with unitary characters, `f^w` is the unique
element of `C` with `lim_{a →_P ∞} [F(m a) - f^w(m a)] = 0` for every `m`. The map `H_M` is
additive and some `a₀` has `⟨α, H_M(a₀)⟩ > 0` for every `α ∈ S`. -/
theorem existsUnique_tendstoZeroAlongParabolic_sub {M : Type*} [Monoid M] (j : A →* M)
    {HM : A → E} (hHM : ∀ a b, HM (a * b) = HM a + HM b) {S : Finset (Module.Dual ℝ E)}
    {a₀ : A} (ha₀ : ∀ α ∈ S, 0 < α (HM a₀)) {ℓ : ι → Module.Dual ℝ E}
    (hℓ : ∀ i, ℓ i ∈ Submodule.span ℝ (S : Set (Module.Dual ℝ E))) {ι' : Type*}
    (ℓ' : ι' → Module.Dual ℝ E) {F fP fw : M → ℂ} {C : Set (M → ℂ)} (hfw : fw ∈ C)
    (hasym : ∀ m, ∃ R : ℝ, ∀ a, (∀ α ∈ S, R < α (HM a)) → F (m * j a) = fP (m * j a))
    (hdec : ∀ m, ∃ (n : ℕ) (χ : Fin n → A →* ℂˣ) (Q : Fin n → MvPolynomial ι ℂ),
      (∀ i, IsDecayingAlongParabolic HM S (χ i)) ∧
        ∀ a, fP (m * j a) - fw (m * j a) = exponentialPolynomial HM ℓ χ Q a)
    (hC : ∀ g₁ ∈ C, ∀ g₂ ∈ C, ∀ m, ∃ (n : ℕ) (χ : Fin n → A →* ℂˣ)
      (Q : Fin n → MvPolynomial ι' ℂ), (∀ i a, ‖(χ i a : ℂ)‖ = 1) ∧
        ∀ a, g₁ (m * j a) - g₂ (m * j a) = exponentialPolynomial HM ℓ' χ Q a) :
    ∃! g, g ∈ C ∧ ∀ m, TendstoZeroAlongParabolic HM S (fun a => F (m * j a) - g (m * j a)) := by
  have hfw' := tendstoZeroAlongParabolic_sub_of_eventually_eq j hℓ hasym hdec
  refine ⟨fw, ⟨hfw, hfw'⟩, fun g ⟨hg, hgl⟩ => ?_⟩
  exact eq_of_tendstoZeroAlongParabolic j hHM ha₀ ℓ' hgl hfw' (hC g hg fw hfw)

end ParabolicLimit

section Counterexample

/-- The character `a ↦ e^{-a₂}` of `ℝ²`, written multiplicatively. -/
def expNegSnd : Multiplicative (ℝ × ℝ) →* ℂˣ where
  toFun a := Units.mk0 ((Real.exp (-(Multiplicative.toAdd a).2) : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne')
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp only [toAdd_mul, Prod.snd_add, neg_add, Real.exp_add, Complex.ofReal_mul,
      Units.val_mul, Units.val_mk0]

/-- The span hypothesis in `tendstoZeroAlongParabolic_exponentialPolynomial` cannot be dropped:
for `A = ℝ²` (written multiplicatively), `H_M = id` and `S = {a ↦ a₂}`, the character
`a ↦ e^{-a₂}` satisfies `IsDecayingAlongParabolic`, but `ϕ(a) = a₁ e^{-a₂}` (the coordinate
`a ↦ a₁` is not in the span of `S`) does not satisfy `lim_{a →_P ∞} ϕ(a) = 0`. -/
theorem not_tendstoZeroAlongParabolic_fst_mul_expNegSnd :
    IsDecayingAlongParabolic (fun a : Multiplicative (ℝ × ℝ) => Multiplicative.toAdd a)
        {LinearMap.snd ℝ ℝ ℝ} expNegSnd ∧
      LinearMap.fst ℝ ℝ ℝ ∉
        Submodule.span ℝ (({LinearMap.snd ℝ ℝ ℝ} : Finset (Module.Dual ℝ (ℝ × ℝ))) :
          Set (Module.Dual ℝ (ℝ × ℝ))) ∧
      ¬ TendstoZeroAlongParabolic (fun a : Multiplicative (ℝ × ℝ) => Multiplicative.toAdd a)
        {LinearMap.snd ℝ ℝ ℝ}
        (exponentialPolynomial (fun a : Multiplicative (ℝ × ℝ) => Multiplicative.toAdd a)
          (fun _ : Unit => LinearMap.fst ℝ ℝ ℝ) (fun _ : Unit => expNegSnd)
          (fun _ => MvPolynomial.X ())) := by
  refine ⟨⟨fun _ => 1, fun _ _ => zero_le_one, ⟨_, Finset.mem_singleton_self _, one_pos⟩,
    fun a => ?_⟩, ?_, ?_⟩
  · simp only [expNegSnd, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Finset.sum_singleton, one_mul,
      LinearMap.snd_apply, le_refl]
  · rw [Finset.coe_singleton, Submodule.mem_span_singleton]
    rintro ⟨r, hr⟩
    have := congrArg (fun φ : Module.Dual ℝ (ℝ × ℝ) => φ (1, 0)) hr
    simp at this
  · intro h
    obtain ⟨R, hR, hR'⟩ := h (1 / 2) (by norm_num) (1 / 2) (by norm_num)
    have := hR' (Multiplicative.ofAdd (Real.exp (R + 1), R + 1))
      (fun α hα => by rw [Finset.mem_singleton.1 hα]; simp)
      (fun α hα β hβ => by
        rw [Finset.mem_singleton.1 hα, Finset.mem_singleton.1 hβ]
        simp only [toAdd_ofAdd, LinearMap.snd_apply]
        linarith)
    have e : exponentialPolynomial (fun a : Multiplicative (ℝ × ℝ) => Multiplicative.toAdd a)
        (fun _ : Unit => LinearMap.fst ℝ ℝ ℝ) (fun _ : Unit => expNegSnd)
        (fun _ => MvPolynomial.X ()) (Multiplicative.ofAdd (Real.exp (R + 1), R + 1)) = 1 := by
      simp only [exponentialPolynomial, Finset.univ_unique, Finset.sum_singleton,
        MvPolynomial.eval_X, toAdd_ofAdd, LinearMap.fst_apply, expNegSnd, MonoidHom.coe_mk,
        OneHom.coe_mk, Units.val_mk0]
      rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
        Complex.ofReal_one]
    rw [e, norm_one] at this
    norm_num at this

end Counterexample

end Langlands.HarishChandraSchwartz
