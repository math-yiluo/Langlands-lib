import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Field

/-! # Uniqueness of the weak constant term (Waldspurger, III.5 and Lemma III.5.1)

Waldspurger, III.5 (printed p. 269): for `f : A_M → ℂ`, one writes `lim_{a →_P ∞} f(a) = 0` if
for all `ε, η > 0` there is `R > 0` such that `|f(a)| < ε` for every `a ∈ A_M` with
(i) `⟨α, H_M(a)⟩ > R` for every `α ∈ Σ(P)` and (ii) `⟨α, H_M(a)⟩ > η ⟨β, H_M(a)⟩` for all
`α, β ∈ Σ(P)`. This limit is `TendstoZeroAlongParabolic`, for an abstract group `A`, a map
`H_M : A → a_M` into a real vector space and a finite set `S` of linear forms in place of `Σ(P)`.

The uniqueness part of the proof of Lemma III.5.1 (printed p. 270) shows that a function
`φ(a) = ∑_{χ ∈ E} Q_χ(H_M(a)) χ(a)` with unitary characters `χ` and polynomials `Q_χ` on `a_M`
satisfying `lim_{a →_P ∞} φ(a) = 0` vanishes. This is
`exponentialPolynomial_eq_zero_of_tendstoZeroAlongParabolic`, for an additive `H_M` and an
`a₀ ∈ A` with `⟨α, H_M(a₀)⟩ > 0` for every `α ∈ S`. The proof restricts `φ` to the rays
`k ↦ b a₀^k` (`TendstoZeroAlongParabolic.tendsto_mul_pow`) and uses that an exponential polynomial
`k ↦ ∑ ν_i^k Q_i(k)` on `ℕ` with `‖ν_i‖ ≥ 1` tending to `0` vanishes
(`sum_pow_mul_eval_eq_zero_of_tendsto`); this replaces the source's argument through the space
spanned by the translates of `φ`. The uniqueness of `f^w_P` itself, for functions whose
differences restrict to such exponential polynomials on every `m A_M`, is
`eq_of_tendstoZeroAlongParabolic`.
-/

noncomputable section

open Filter Polynomial Topology

namespace Langlands.HarishChandraSchwartz

section ExponentialSequence

variable {𝕜 : Type*} [NormedField 𝕜] [CharZero 𝕜] {ι : Type*} [Fintype ι]

open scoped Classical in
/-- The induction behind `eq_zero_of_tendsto_sum_pow_mul_eval`, on a bound `N` for the total
size `∑ i, (natDegree (Q i) + 1)` of the nonzero coefficient polynomials. -/
theorem eq_zero_of_tendsto_sum_pow_mul_eval_of_le {ν : ι → 𝕜} (hν : Function.Injective ν)
    (hν1 : ∀ i, 1 ≤ ‖ν i‖) (N : ℕ) :
    ∀ Q : ι → 𝕜[X], ∑ i, (if Q i = 0 then 0 else (Q i).natDegree + 1) ≤ N →
      Tendsto (fun k : ℕ => ∑ i, ν i ^ k * (Q i).eval (k : 𝕜)) atTop (𝓝 0) →
        ∀ i, Q i = 0 := by
  classical
  have hν0 : ∀ i, ν i ≠ 0 := fun i h0 => by
    have := hν1 i
    rw [h0, norm_zero] at this
    linarith
  induction N with
  | zero =>
    intro Q hQ _ i
    have := (Finset.sum_eq_zero_iff.1 (Nat.le_zero.1 hQ)) i (Finset.mem_univ i)
    by_contra hi
    simp [hi] at this
  | succ N ih =>
    intro Q hQ h
    by_contra hne
    obtain ⟨j, hj⟩ := not_forall.1 hne
    -- the difference operator `a ↦ (k ↦ a (k + 1) - ν j * a k)` on coefficient polynomials
    set Q' : ι → 𝕜[X] := fun i => C (ν i) * taylor 1 (Q i) - C (ν j) * Q i with hQ'
    have e : ∀ k : ℕ, ∑ i, ν i ^ k * (Q' i).eval (k : 𝕜) =
        ∑ i, ν i ^ (k + 1) * (Q i).eval ((k + 1 : ℕ) : 𝕜) -
          ν j * ∑ i, ν i ^ k * (Q i).eval (k : 𝕜) := by
      intro k
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hQ', eval_sub, eval_mul, eval_C, taylor_eval, Nat.cast_succ]
      ring
    have h' : Tendsto (fun k : ℕ => ∑ i, ν i ^ k * (Q' i).eval (k : 𝕜)) atTop (𝓝 0) := by
      simp only [e]
      have := (h.comp (tendsto_add_atTop_nat 1)).sub (h.const_mul (ν j))
      simpa using this
    have hle : ∀ i, (if Q' i = 0 then 0 else (Q' i).natDegree + 1) ≤
        (if Q i = 0 then 0 else (Q i).natDegree + 1) := by
      intro i
      by_cases hi : Q i = 0
      · have : Q' i = 0 := by simp [hQ', hi]
        simp [this, hi]
      · have hdeg : (Q' i).natDegree ≤ (Q i).natDegree := by
          refine (natDegree_sub_le_of_le ((natDegree_C_mul_le _ _).trans
            (natDegree_taylor _ _).le) (natDegree_C_mul_le _ _)).trans ?_
          simp
        simp only [hi, ↓reduceIte]
        split_ifs <;> omega
    have hQ'j : Q' j = C (ν j) * (taylor 1 (Q j) - Q j) := by
      simp only [hQ', mul_sub]
    have hlt : (if Q' j = 0 then 0 else (Q' j).natDegree + 1) <
        (if Q j = 0 then 0 else (Q j).natDegree + 1) := by
      simp only [hj, ↓reduceIte]
      split_ifs with h0
      · omega
      · have hD : taylor 1 (Q j) - Q j ≠ 0 := by
          intro hD
          apply h0
          rw [hQ'j, hD, mul_zero]
        have hdeg : (taylor 1 (Q j) - Q j).degree < (Q j).degree := by
          have := degree_sub_lt_left (degree_taylor (Q j) 1) (mt (taylor_eq_zero 1 (Q j)).1 hj)
            (leadingCoeff_taylor 1 (Q j))
          rwa [degree_taylor] at this
        have := natDegree_lt_natDegree hD hdeg
        have h2 : (Q' j).natDegree ≤ (taylor 1 (Q j) - Q j).natDegree := by
          rw [hQ'j]
          exact natDegree_C_mul_le _ _
        omega
    have hsum : ∑ i, (if Q' i = 0 then 0 else (Q' i).natDegree + 1) ≤ N := by
      have := Finset.sum_lt_sum (s := Finset.univ) (fun i _ => hle i)
        ⟨j, Finset.mem_univ j, hlt⟩
      omega
    have hQ'0 := ih Q' hsum h'
    -- the coefficient polynomials other than `Q j` vanish
    have hother : ∀ i, i ≠ j → Q i = 0 := by
      intro i hij
      by_contra hi
      have heq : C (ν i) * taylor 1 (Q i) = C (ν j) * Q i := sub_eq_zero.1 (hQ'0 i)
      have hlc := congrArg leadingCoeff heq
      simp only [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_taylor] at hlc
      exact hij (hν (mul_right_cancel₀ (leadingCoeff_ne_zero.2 hi) hlc))
    -- `Q j` is invariant under `X ↦ X + 1`, hence constant on `ℕ`
    have htaylor : taylor 1 (Q j) = Q j := by
      have := hQ'0 j
      rw [hQ'j, mul_eq_zero] at this
      exact sub_eq_zero.1 (this.resolve_left (by simpa using hν0 j))
    have hconst : ∀ k : ℕ, (Q j).eval (k : 𝕜) = (Q j).eval 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ihk =>
        rw [Nat.cast_succ, ← taylor_eval, htaylor, ihk]
    -- the sequence reduces to `ν j ^ k * Q j (0)`, whose norm is at least `‖Q j (0)‖`
    have hseq : ∀ k : ℕ, ∑ i, ν i ^ k * (Q i).eval (k : 𝕜) = ν j ^ k * (Q j).eval 0 := by
      intro k
      rw [Finset.sum_eq_single j (fun i _ hij => by rw [hother i hij, eval_zero, mul_zero])
        (fun hj' => absurd (Finset.mem_univ j) hj'), hconst k]
    have hzero : (Q j).eval 0 = 0 := by
      have hnorm := h.norm
      simp only [hseq, norm_zero] at hnorm
      have hle0 : ‖(Q j).eval 0‖ ≤ 0 := by
        refine ge_of_tendsto' hnorm fun k => ?_
        rw [norm_mul, norm_pow]
        exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (hν1 j))
      exact norm_le_zero_iff.1 hle0
    apply hj
    refine eq_zero_of_infinite_isRoot _ ((Set.infinite_range_of_injective
      Nat.cast_injective).mono ?_)
    rintro _ ⟨k, rfl⟩
    exact (hconst k).trans hzero

/-- An exponential polynomial `k ↦ ∑ i, ν i ^ k * Q i (k)` on `ℕ`, with distinct `ν i` of norm at
least `1`, that tends to `0` has all coefficient polynomials `Q i` equal to zero. -/
theorem eq_zero_of_tendsto_sum_pow_mul_eval {ν : ι → 𝕜} (hν : Function.Injective ν)
    (hν1 : ∀ i, 1 ≤ ‖ν i‖) {Q : ι → 𝕜[X]}
    (h : Tendsto (fun k : ℕ => ∑ i, ν i ^ k * (Q i).eval (k : 𝕜)) atTop (𝓝 0)) :
    ∀ i, Q i = 0 :=
  eq_zero_of_tendsto_sum_pow_mul_eval_of_le hν hν1 _ Q le_rfl h

/-- An exponential polynomial `k ↦ ∑ i, ν i ^ k * Q i (k)` on `ℕ`, with all `ν i` of norm at least
`1` (not necessarily distinct), that tends to `0` vanishes identically. -/
theorem sum_pow_mul_eval_eq_zero_of_tendsto {ν : ι → 𝕜} (hν1 : ∀ i, 1 ≤ ‖ν i‖) {Q : ι → 𝕜[X]}
    (h : Tendsto (fun k : ℕ => ∑ i, ν i ^ k * (Q i).eval (k : 𝕜)) atTop (𝓝 0)) (k : ℕ) :
    ∑ i, ν i ^ k * (Q i).eval (k : 𝕜) = 0 := by
  classical
  -- group the indices with the same ratio `ν i`
  set V : Finset 𝕜 := Finset.univ.image ν
  let R : V → 𝕜[X] := fun v => ∑ i ∈ Finset.univ.filter (fun i => ν i = v), Q i
  have hgroup : ∀ k : ℕ, ∑ i, ν i ^ k * (Q i).eval (k : 𝕜) =
      ∑ v : V, (v : 𝕜) ^ k * (R v).eval (k : 𝕜) := by
    intro k
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := V) (g := ν)
      (fun i _ => Finset.mem_image_of_mem ν (Finset.mem_univ i))]
    rw [← Finset.sum_coe_sort V]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [R, eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  have hR := eq_zero_of_tendsto_sum_pow_mul_eval (ν := fun v : V => (v : 𝕜))
    Subtype.val_injective (fun v => by
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 v.2
      rw [← hi]
      exact hν1 i) (Q := R) (by simpa only [hgroup] using h)
  rw [hgroup k]
  simp [hR]

end ExponentialSequence

section ParabolicLimit

variable {A E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Waldspurger III.5 (printed p. 269): `lim_{a →_P ∞} f(a) = 0`, i.e. for all `ε, η > 0` there
is `R > 0` such that `|f(a)| < ε` for every `a` with (i) `⟨α, H_M(a)⟩ > R` for every `α ∈ S` and
(ii) `⟨α, H_M(a)⟩ > η ⟨β, H_M(a)⟩` for all `α, β ∈ S`. Here `HM` plays the role of `H_M` and the
finite set `S` of linear forms the role of `Σ(P)`. -/
def TendstoZeroAlongParabolic (HM : A → E) (S : Finset (Module.Dual ℝ E)) (f : A → ℂ) :
    Prop :=
  ∀ ε > 0, ∀ η > 0, ∃ R > 0, ∀ a : A, (∀ α ∈ S, R < α (HM a)) →
    (∀ α ∈ S, ∀ β ∈ S, η * β (HM a) < α (HM a)) → ‖f a‖ < ε

/-- The difference of two functions with `lim_{a →_P ∞} = 0` has `lim_{a →_P ∞} = 0`. -/
theorem TendstoZeroAlongParabolic.sub {HM : A → E} {S : Finset (Module.Dual ℝ E)}
    {f g : A → ℂ} (hf : TendstoZeroAlongParabolic HM S f)
    (hg : TendstoZeroAlongParabolic HM S g) :
    TendstoZeroAlongParabolic HM S (fun a => f a - g a) := by
  intro ε hε η hη
  obtain ⟨R₁, hR₁, h₁⟩ := hf (ε / 2) (half_pos hε) η hη
  obtain ⟨R₂, hR₂, h₂⟩ := hg (ε / 2) (half_pos hε) η hη
  refine ⟨max R₁ R₂, lt_max_of_lt_left hR₁, fun a hi hii => ?_⟩
  have e₁ := h₁ a (fun α hα => (le_max_left _ _).trans_lt (hi α hα)) hii
  have e₂ := h₂ a (fun α hα => (le_max_right _ _).trans_lt (hi α hα)) hii
  calc ‖f a - g a‖ ≤ ‖f a‖ + ‖g a‖ := norm_sub_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add e₁ e₂
    _ = ε := add_halves ε

/-- An affine function `k ↦ c + k d` on `ℕ` with `d > 0` eventually exceeds every bound. -/
theorem eventually_lt_add_natCast_mul {c d R : ℝ} (hd : 0 < d) :
    ∀ᶠ k : ℕ in atTop, R < c + k * d :=
  (tendsto_atTop_add_const_left _ c
    ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hd)).eventually_gt_atTop R

variable [CommGroup A]

/-- An additive `H_M` maps `b a₀^k` to `H_M(b) + k H_M(a₀)`. -/
theorem apply_mul_pow_of_map_mul {HM : A → E} (hHM : ∀ a b, HM (a * b) = HM a + HM b)
    (b a₀ : A) (k : ℕ) : HM (b * a₀ ^ k) = HM b + (k : ℝ) • HM a₀ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, hHM, ih, Nat.cast_succ, add_smul, one_smul, add_assoc]

/-- Along a ray `k ↦ b a₀^k` with `⟨α, H_M(a₀)⟩ > 0` for every `α ∈ S`, a function with
`lim_{a →_P ∞} f(a) = 0` tends to `0`. -/
theorem TendstoZeroAlongParabolic.tendsto_mul_pow {HM : A → E}
    (hHM : ∀ a b, HM (a * b) = HM a + HM b) {S : Finset (Module.Dual ℝ E)} {f : A → ℂ}
    (hf : TendstoZeroAlongParabolic HM S f) {a₀ : A} (ha₀ : ∀ α ∈ S, 0 < α (HM a₀)) (b : A) :
    Tendsto (fun k : ℕ => f (b * a₀ ^ k)) atTop (𝓝 0) := by
  -- an `η₀ > 0` with `η₀ ⟨β, H_M(a₀)⟩ < ⟨α, H_M(a₀)⟩` for all `α, β ∈ S`
  have hη : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η ∧ ∀ α ∈ S, ∀ β ∈ S, η * β (HM a₀) < α (HM a₀) := by
    refine (eventually_nhdsWithin_of_forall fun _ h => h).and (nhdsWithin_le_nhds ?_)
    refine (eventually_all_finset S).2 fun α hα => (eventually_all_finset S).2 fun β _ => ?_
    have hc : Continuous fun η : ℝ => η * β (HM a₀) := continuous_id.mul continuous_const
    have := hc.tendsto 0
    simp only [zero_mul] at this
    exact this.eventually (gt_mem_nhds (ha₀ α hα))
  obtain ⟨η₀, hη₀, hη₀S⟩ := hη.exists
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, -, hR⟩ := hf ε hε η₀ hη₀
  have hev : ∀ᶠ k : ℕ in atTop, (∀ α ∈ S, R < α (HM (b * a₀ ^ k))) ∧
      ∀ α ∈ S, ∀ β ∈ S, η₀ * β (HM (b * a₀ ^ k)) < α (HM (b * a₀ ^ k)) := by
    simp only [apply_mul_pow_of_map_mul hHM, map_add, map_smul, smul_eq_mul]
    refine ((eventually_all_finset S).2 fun α hα => ?_).and
      ((eventually_all_finset S).2 fun α hα => (eventually_all_finset S).2 fun β hβ => ?_)
    · filter_upwards [eventually_lt_add_natCast_mul (c := α (HM b)) (R := R) (ha₀ α hα)]
        with k hk
      linarith
    · filter_upwards [eventually_lt_add_natCast_mul (c := α (HM b) - η₀ * β (HM b)) (R := 0)
        (sub_pos.2 (hη₀S α hα β hβ))] with k hk
      linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  exact ⟨N, fun k hk => by
    rw [dist_zero_right]
    exact hR _ (hN k hk).1 (hN k hk).2⟩

variable {ι κ : Type*} [Fintype κ]

/-- The function `a ↦ ∑_j χ_j(a) Q_j(H_M(a))` of Waldspurger I.2 and of (1) in the proof of
Lemma III.5.1, for characters `χ_j : A → ℂˣ` and polynomials `Q_j` on `a_M` given as polynomials
`Q j` in the linear coordinates `ℓ i`. -/
def exponentialPolynomial (HM : A → E) (ℓ : ι → Module.Dual ℝ E) (χ : κ → A →* ℂˣ)
    (Q : κ → MvPolynomial ι ℂ) (a : A) : ℂ :=
  ∑ j, (χ j a : ℂ) * MvPolynomial.eval (fun i => ((ℓ i (HM a) : ℝ) : ℂ)) (Q j)

/-- A polynomial in linear coordinates, restricted to an affine line `x + k v`, `k ∈ ℕ`, is a
polynomial in `k`. -/
theorem exists_eval_add_natCast_smul (ℓ : ι → Module.Dual ℝ E) (x v : E)
    (p : MvPolynomial ι ℂ) :
    ∃ P : ℂ[X], ∀ k : ℕ,
      MvPolynomial.eval (fun i => ((ℓ i (x + (k : ℝ) • v) : ℝ) : ℂ)) p = P.eval (k : ℂ) := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨C c, fun k => by simp⟩
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp
    obtain ⟨P', hP'⟩ := hq
    exact ⟨P + P', fun k => by rw [map_add, hP k, hP' k, eval_add]⟩
  | mul_X p i hp =>
    obtain ⟨P, hP⟩ := hp
    refine ⟨P * (C ((ℓ i x : ℝ) : ℂ) + C ((ℓ i v : ℝ) : ℂ) * X), fun k => ?_⟩
    rw [map_mul, hP k, MvPolynomial.eval_X]
    simp only [eval_mul, eval_add, eval_C, eval_X, map_add, map_smul, smul_eq_mul]
    push_cast
    ring

/-- Uniqueness core of Waldspurger, Lemma III.5.1 (printed p. 270): if
`φ(a) = ∑_j χ_j(a) Q_j(H_M(a))` with unitary characters `χ_j` satisfies `lim_{a →_P ∞} φ(a) = 0`,
then `φ = 0`. The map `H_M` is additive and some `a₀` has `⟨α, H_M(a₀)⟩ > 0` for every `α ∈ S`. -/
theorem exponentialPolynomial_eq_zero_of_tendstoZeroAlongParabolic {HM : A → E}
    (hHM : ∀ a b, HM (a * b) = HM a + HM b) {S : Finset (Module.Dual ℝ E)} {a₀ : A}
    (ha₀ : ∀ α ∈ S, 0 < α (HM a₀)) (ℓ : ι → Module.Dual ℝ E) {χ : κ → A →* ℂˣ}
    (hχ : ∀ j a, ‖(χ j a : ℂ)‖ = 1) (Q : κ → MvPolynomial ι ℂ)
    (h : TendstoZeroAlongParabolic HM S (exponentialPolynomial HM ℓ χ Q)) (b : A) :
    exponentialPolynomial HM ℓ χ Q b = 0 := by
  choose P hP using fun j => exists_eval_add_natCast_smul ℓ (HM b) (HM a₀) (Q j)
  have hray : ∀ k : ℕ, exponentialPolynomial HM ℓ χ Q (b * a₀ ^ k) =
      ∑ j, (χ j a₀ : ℂ) ^ k * (C (χ j b : ℂ) * P j).eval (k : ℂ) := by
    intro k
    simp only [exponentialPolynomial, apply_mul_pow_of_map_mul hHM, hP, map_mul, map_pow,
      Units.val_mul, Units.val_pow_eq_pow_val, eval_mul, eval_C]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hlim := h.tendsto_mul_pow hHM ha₀ b
  simp only [hray] at hlim
  have := sum_pow_mul_eval_eq_zero_of_tendsto (fun j => (hχ j a₀).ge) hlim 0
  rw [← hray 0, pow_zero, mul_one] at this
  exact this

/-- Uniqueness in Waldspurger, Lemma III.5.1 (printed p. 270), for functions on a monoid `M`
containing `A` through `j`: if `lim_{a →_P ∞} [F(m a) - f_i(m a)] = 0` for `i = 1, 2` and every
`m ∈ M`, and for every `m` the difference `a ↦ f_1(m a) - f_2(m a)` is an exponential polynomial
with unitary characters, then `f_1 = f_2`. In the source `F(g) = δ_P(g)^{-1/2} f(g)`. -/
theorem eq_of_tendstoZeroAlongParabolic {M : Type*} [Monoid M] (j : A →* M) {HM : A → E}
    (hHM : ∀ a b, HM (a * b) = HM a + HM b) {S : Finset (Module.Dual ℝ E)} {a₀ : A}
    (ha₀ : ∀ α ∈ S, 0 < α (HM a₀)) (ℓ : ι → Module.Dual ℝ E) {F f₁ f₂ : M → ℂ}
    (h₁ : ∀ m, TendstoZeroAlongParabolic HM S (fun a => F (m * j a) - f₁ (m * j a)))
    (h₂ : ∀ m, TendstoZeroAlongParabolic HM S (fun a => F (m * j a) - f₂ (m * j a)))
    (hexp : ∀ m, ∃ (n : ℕ) (χ : Fin n → A →* ℂˣ) (Q : Fin n → MvPolynomial ι ℂ),
      (∀ i a, ‖(χ i a : ℂ)‖ = 1) ∧
        ∀ a, f₁ (m * j a) - f₂ (m * j a) = exponentialPolynomial HM ℓ χ Q a) :
    f₁ = f₂ := by
  funext m
  obtain ⟨n, χ, Q, hχ, hφ⟩ := hexp m
  have hlim : TendstoZeroAlongParabolic HM S (exponentialPolynomial HM ℓ χ Q) := by
    have := (h₂ m).sub (h₁ m)
    have e : (fun a => F (m * j a) - f₂ (m * j a) - (F (m * j a) - f₁ (m * j a))) =
        exponentialPolynomial HM ℓ χ Q := by
      funext a
      rw [← hφ a]
      ring
    rwa [e] at this
  have h1 := hφ 1
  rw [exponentialPolynomial_eq_zero_of_tendstoZeroAlongParabolic hHM ha₀ ℓ hχ Q hlim 1,
    map_one, mul_one] at h1
  exact sub_eq_zero.1 h1

end ParabolicLimit

end Langlands.HarishChandraSchwartz
