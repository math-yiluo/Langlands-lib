import Langlands.Global.RankinSelberg.EqualAnalyticStatement

/-! # Entire functions plus two simple fractions

For an entire `G` and `f(s) = G(s) + a₁/(m s + b₁) + a₂/(m s + b₂)` with `m ≠ 0`:

* `f` has at most simple poles in any set containing `-b₁/m` and `-b₂/m`
  (`hasAtMostSimplePolesIn_two`), and an entire function has at most simple poles in any set
  (`hasAtMostSimplePolesIn_entire`);
* if `G` is bounded in vertical strips, so is `f` away from such a set
  (`boundedInVerticalStripsAwayFrom_two`, `boundedInVerticalStripsAwayFrom_entire`).
-/

noncomputable section
open Filter Topology

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

/-- Near any point `p`, the quotient `(s - p)/(s - s₀)` is bounded by one. -/
theorem exists_norm_div_le_one (p s₀ : ℂ) :
    ∃ ε > 0, ∀ s : ℂ, ‖s - p‖ < ε → ‖(s - p) / (s - s₀)‖ ≤ 1 := by
  by_cases h : p = s₀
  · subst h
    refine ⟨1, one_pos, fun s _ => ?_⟩
    by_cases hs : s - p = 0
    · simp [hs]
    · rw [div_self hs, norm_one]
  · have hpos : 0 < ‖p - s₀‖ := norm_pos_iff.2 (sub_ne_zero.2 h)
    refine ⟨‖p - s₀‖ / 2, by positivity, fun s hs => ?_⟩
    have h1 : ‖p - s₀‖ ≤ ‖s - p‖ + ‖s - s₀‖ := by
      calc ‖p - s₀‖ = ‖-(s - p) + (s - s₀)‖ := by congr 1; ring
        _ ≤ ‖-(s - p)‖ + ‖s - s₀‖ := norm_add_le _ _
        _ = ‖s - p‖ + ‖s - s₀‖ := by rw [norm_neg]
    have h2 : ‖s - p‖ < ‖s - s₀‖ := by linarith
    rw [norm_div]
    exact div_le_one_of_le₀ h2.le (norm_nonneg _)

theorem frac_eq (a m b s : ℂ) (hm : m ≠ 0) :
    a / (m * s + b) = (a / m) / (s - (-b / m)) := by
  have h : s - (-b / m) = (m * s + b) / m := by
    field_simp
    ring
  rw [h, div_div_div_cancel_right₀ hm]

/-- An entire function has at most simple poles in any set. -/
theorem hasAtMostSimplePolesIn_entire {G : ℂ → ℂ} (hG : Differentiable ℂ G) (P : Set ℂ) :
    HasAtMostSimplePolesIn G P := by
  refine ⟨hG.differentiableOn, fun p _ => ?_⟩
  have hc := hG.continuous.continuousAt (x := p)
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, hδb⟩ := hc 1 one_pos
  refine ⟨min δ 1, lt_min hδ one_pos, ‖G p‖ + 1, fun s _ hs => ?_⟩
  have hs1 : ‖s - p‖ < δ := lt_of_lt_of_le hs (min_le_left _ _)
  have hs2 : ‖s - p‖ ≤ 1 := (lt_of_lt_of_le hs (min_le_right _ _)).le
  have hG1 : ‖G s‖ ≤ ‖G p‖ + 1 := by
    have := hδb (by rwa [dist_eq_norm])
    rw [dist_eq_norm] at this
    have h3 := norm_le_insert' (G s) (G p)
    linarith [norm_sub_rev (G s) (G p)]
  rw [norm_mul]
  calc ‖s - p‖ * ‖G s‖ ≤ 1 * (‖G p‖ + 1) :=
        mul_le_mul hs2 hG1 (norm_nonneg _) zero_le_one
    _ = ‖G p‖ + 1 := one_mul _

/-- **Simple poles of an entire function plus two simple fractions.** -/
theorem hasAtMostSimplePolesIn_two {G : ℂ → ℂ} (hG : Differentiable ℂ G) {a₁ a₂ m b₁ b₂ : ℂ}
    (hm : m ≠ 0) {P : Set ℂ} (h₁ : -b₁ / m ∈ P) (h₂ : -b₂ / m ∈ P) :
    HasAtMostSimplePolesIn (fun s => G s + a₁ / (m * s + b₁) + a₂ / (m * s + b₂)) P := by
  have hden : ∀ b : ℂ, ∀ s ∉ P, -b / m ∈ P → m * s + b ≠ 0 := by
    intro b s hs hb h
    apply hs
    have : s = -b / m := by
      rw [eq_div_iff hm]
      linear_combination h
    rw [this]
    exact hb
  refine ⟨fun s hs => ?_, fun p _ => ?_⟩
  · have d₁ : DifferentiableAt ℂ (fun s => a₁ / (m * s + b₁)) s :=
      (differentiableAt_const _).div ((differentiableAt_const _).mul differentiableAt_id
        |>.add (differentiableAt_const _)) (hden b₁ s hs h₁)
    have d₂ : DifferentiableAt ℂ (fun s => a₂ / (m * s + b₂)) s :=
      (differentiableAt_const _).div ((differentiableAt_const _).mul differentiableAt_id
        |>.add (differentiableAt_const _)) (hden b₂ s hs h₂)
    exact ((hG s).add d₁ |>.add d₂).differentiableWithinAt
  · obtain ⟨ε₀, hε₀, C₀, hC₀⟩ := (hasAtMostSimplePolesIn_entire hG {p}).2 p rfl
    obtain ⟨ε₁, hε₁, h₁'⟩ := exists_norm_div_le_one p (-b₁ / m)
    obtain ⟨ε₂, hε₂, h₂'⟩ := exists_norm_div_le_one p (-b₂ / m)
    refine ⟨min ε₀ (min ε₁ ε₂), lt_min hε₀ (lt_min hε₁ hε₂),
      C₀ + ‖a₁ / m‖ + ‖a₂ / m‖, fun s hsp hs => ?_⟩
    have hs0 : ‖s - p‖ < ε₀ := lt_of_lt_of_le hs (min_le_left _ _)
    have hs1 : ‖s - p‖ < ε₁ := lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_left _ _))
    have hs2 : ‖s - p‖ < ε₂ := lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_right _ _))
    have e : (s - p) * (G s + a₁ / (m * s + b₁) + a₂ / (m * s + b₂)) =
        (s - p) * G s + a₁ / m * ((s - p) / (s - (-b₁ / m))) +
          a₂ / m * ((s - p) / (s - (-b₂ / m))) := by
      rw [frac_eq a₁ m b₁ s hm, frac_eq a₂ m b₂ s hm]
      ring
    rw [e]
    refine (norm_add₃_le).trans ?_
    rw [norm_mul (a₁ / m), norm_mul (a₂ / m)]
    have k₁ := mul_le_mul_of_nonneg_left (h₁' s hs1) (norm_nonneg (a₁ / m))
    have k₂ := mul_le_mul_of_nonneg_left (h₂' s hs2) (norm_nonneg (a₂ / m))
    have k₀ := hC₀ s hsp hs0
    linarith

/-- An entire function bounded in vertical strips is bounded away from any set. -/
theorem boundedInVerticalStripsAwayFrom_entire {G : ℂ → ℂ}
    (hG : ∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖G s‖ ≤ C) (P : Set ℂ) :
    BoundedInVerticalStripsAwayFrom G P := by
  intro a b _ δ _
  obtain ⟨C, hC0, hC⟩ := hG a b
  exact ⟨C, hC0, fun s ha hb _ => hC s ha hb⟩

/-- **Boundedness in strips of an entire function plus two simple fractions.** -/
theorem boundedInVerticalStripsAwayFrom_two {G : ℂ → ℂ}
    (hG : ∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖G s‖ ≤ C)
    {a₁ a₂ m b₁ b₂ : ℂ} (hm : m ≠ 0) {P : Set ℂ} (h₁ : -b₁ / m ∈ P) (h₂ : -b₂ / m ∈ P) :
    BoundedInVerticalStripsAwayFrom (fun s => G s + a₁ / (m * s + b₁) + a₂ / (m * s + b₂)) P := by
  intro a b _ δ hδ
  obtain ⟨C, hC0, hC⟩ := hG a b
  refine ⟨C + ‖a₁ / m‖ / δ + ‖a₂ / m‖ / δ, by positivity, fun s ha hb hP => ?_⟩
  have hfrac : ∀ (c b' : ℂ), -b' / m ∈ P → ‖c / (m * s + b')‖ ≤ ‖c / m‖ / δ := by
    intro c b' hb'
    rw [frac_eq c m b' s hm, norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hδ (hP _ hb')
  refine (norm_add₃_le).trans ?_
  linarith [hC s ha hb, hfrac a₁ b₁ h₁, hfrac a₂ b₂ h₂]

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
