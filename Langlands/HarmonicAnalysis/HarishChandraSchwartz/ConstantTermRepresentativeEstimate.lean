import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermBound

/-! # The scalar constant-term estimate on a set of representatives -/

noncomputable section

universe u

open scoped ENNReal NNReal
open MeasureTheory

namespace Langlands.HarishChandraSchwartz

variable {G : Type u} [Group G] [MeasurableSpace G]
  {M U : Subgroup G} {ν : Measure U} {δ : M →* ℝ≥0ˣ}
  {Ξ σ : G → ℝ} {ΞM : M → ℝ}

/-- The scalar part of Proposition II.4.5, before the independent compact
cover reduction. Only the four analytic bounds and their sign hypotheses
are required here. -/
theorem constantTermRepresentativeEstimate_of_bounds {S : Set M}
    {e eM : M → ℝ} {w : U → ℝ}
    (hσ : ∀ g, 0 ≤ σ g) (hΞM : ∀ m, 0 ≤ ΞM m) (he : ∀ m ∈ S, 0 ≤ e m)
    (hw : ∀ u, 0 ≤ w u) (heM : ∀ m ∈ S, e m * NNReal.sqrt (δ m) ≤ eM m)
    (h44 : UnipotentXiBound Ξ σ S e w) (h31 : SigmaProductBound M U σ)
    (h11 : XiLowerBound ΞM S eM) (h42 : UnipotentWeightIntegrable ν w σ) :
    ∀ d : ℝ, ∃ d' : ℝ, ∃ c : ℝ≥0, ∀ m ∈ S,
      (NNReal.sqrt (δ m) : ℝ≥0∞) *
        ∫⁻ u : U, ENNReal.ofReal
          (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-d')) ∂ν ≤
            c * ENNReal.ofReal (ΞM m * (1 + σ m) ^ (-d)) := by
  obtain ⟨D, c₁, h44⟩ := h44
  obtain ⟨C₂, hC₂, h31⟩ := h31
  obtain ⟨C₃, h11⟩ := h11
  obtain ⟨d₂, hI₂⟩ := h42
  intro d
  set r := max (max d d₂) 0 with hr_def
  have hr : 0 ≤ r := le_max_right _ _
  have hdr : d ≤ r := (le_max_left _ _).trans (le_max_left _ _)
  have hd₂r : d₂ ≤ r := (le_max_right _ _).trans (le_max_left _ _)
  set c₁' := max c₁ 0
  set C₃' := max C₃ 0
  set K : ℝ := c₁' * C₂ ^ (-(2 * r)) * C₃'
  have hK : 0 ≤ K := by positivity
  set I : ℝ≥0∞ := ∫⁻ u, ENNReal.ofReal (w u * (1 + σ u) ^ (-r)) ∂ν
  have hI : I ≠ ⊤ := by
    refine (lt_of_le_of_lt (lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_) hI₂).ne
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith [hσ u]) (by linarith)) (hw u)
  refine ⟨D + 2 * r, (Real.toNNReal K) * I.toNNReal, ?_⟩
  -- the bound at the points of `S`
  have key : ∀ s ∈ S, (NNReal.sqrt (δ s) : ℝ≥0∞) *
      ∫⁻ u : U, ENNReal.ofReal (Ξ ((s : G) * u) * (1 + σ ((s : G) * u)) ^ (-(D + 2 * r))) ∂ν
      ≤ ENNReal.ofReal K * I * ENNReal.ofReal (ΞM s * (1 + σ s) ^ (-d)) := by
    intro s hs
    set A : ℝ := c₁' * C₂ ^ (-(2 * r)) * e s * (1 + σ s) ^ (-r)
    have hA : 0 ≤ A := by
      have := he s hs
      have := hσ s
      positivity
    have hpt : ∀ u : U, Ξ ((s : G) * u) * (1 + σ ((s : G) * u)) ^ (-(D + 2 * r)) ≤
        A * (w u * (1 + σ u) ^ (-r)) := by
      intro u
      have ht : 0 < 1 + σ ((s : G) * u) := by linarith [hσ ((s : G) * u)]
      have h1 : Ξ ((s : G) * u) ≤ c₁' * e s * w u * (1 + σ ((s : G) * u)) ^ D := by
        refine (h44 s hs u).trans ?_
        have := he s hs
        have := hw u
        gcongr
        exact le_max_left _ _
      have h2 : Ξ ((s : G) * u) * (1 + σ ((s : G) * u)) ^ (-(D + 2 * r)) ≤
          c₁' * e s * w u * (1 + σ ((s : G) * u)) ^ (-(2 * r)) := by
        calc Ξ ((s : G) * u) * (1 + σ ((s : G) * u)) ^ (-(D + 2 * r))
            ≤ c₁' * e s * w u * (1 + σ ((s : G) * u)) ^ D *
                (1 + σ ((s : G) * u)) ^ (-(D + 2 * r)) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = c₁' * e s * w u * (1 + σ ((s : G) * u)) ^ (-(2 * r)) := by
              rw [mul_assoc, ← Real.rpow_add ht]
              ring_nf
      have h3 := one_add_rpow_neg_le (hσ s) (hσ u) hC₂ hr (h31 s u)
      calc Ξ ((s : G) * u) * (1 + σ ((s : G) * u)) ^ (-(D + 2 * r))
          ≤ c₁' * e s * w u * (1 + σ ((s : G) * u)) ^ (-(2 * r)) := h2
        _ ≤ c₁' * e s * w u * (C₂ ^ (-(2 * r)) * ((1 + σ s) ^ (-r) * (1 + σ u) ^ (-r))) := by
            have := he s hs
            have := hw u
            gcongr
        _ = A * (w u * (1 + σ u) ^ (-r)) := by ring
    have hint : ∫⁻ u : U, ENNReal.ofReal (Ξ ((s : G) * u) *
        (1 + σ ((s : G) * u)) ^ (-(D + 2 * r))) ∂ν ≤ ENNReal.ofReal A * I := by
      calc ∫⁻ u : U, ENNReal.ofReal (Ξ ((s : G) * u) *
            (1 + σ ((s : G) * u)) ^ (-(D + 2 * r))) ∂ν
          ≤ ∫⁻ u : U, ENNReal.ofReal A * ENNReal.ofReal (w u * (1 + σ u) ^ (-r)) ∂ν := by
            refine lintegral_mono fun u => ?_
            rw [← ENNReal.ofReal_mul hA]
            exact ENNReal.ofReal_le_ofReal (hpt u)
        _ = ENNReal.ofReal A * I := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have hsq : (NNReal.sqrt (δ s) : ℝ) * A ≤ K * (ΞM s * (1 + σ s) ^ (-d)) := by
      have hσs := hσ s
      have h1 : (NNReal.sqrt (δ s) : ℝ) * A =
          c₁' * C₂ ^ (-(2 * r)) * (e s * NNReal.sqrt (δ s)) * (1 + σ s) ^ (-r) := by ring
      have h2 : e s * NNReal.sqrt (δ s) ≤ C₃' * ΞM s :=
        (heM s hs).trans ((h11 s hs).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (hΞM s)))
      have h3 : (1 + σ s) ^ (-r) ≤ (1 + σ s) ^ (-d) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      rw [h1]
      calc c₁' * C₂ ^ (-(2 * r)) * (e s * NNReal.sqrt (δ s)) * (1 + σ s) ^ (-r)
          ≤ c₁' * C₂ ^ (-(2 * r)) * (C₃' * ΞM s) * (1 + σ s) ^ (-d) := by
            have := hΞM s
            have : 0 ≤ e s * NNReal.sqrt (δ s) := mul_nonneg (he s hs) (NNReal.coe_nonneg _)
            gcongr
        _ = K * (ΞM s * (1 + σ s) ^ (-d)) := by ring
    calc (NNReal.sqrt (δ s) : ℝ≥0∞) *
          ∫⁻ u : U, ENNReal.ofReal (Ξ ((s : G) * u) *
            (1 + σ ((s : G) * u)) ^ (-(D + 2 * r))) ∂ν
        ≤ (NNReal.sqrt (δ s) : ℝ≥0∞) * (ENNReal.ofReal A * I) := by gcongr
      _ = ENNReal.ofReal ((NNReal.sqrt (δ s) : ℝ) * A) * I := by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal, mul_assoc]
      _ ≤ ENNReal.ofReal (K * (ΞM s * (1 + σ s) ^ (-d))) * I := by
          gcongr
      _ = ENNReal.ofReal K * I * ENNReal.ofReal (ΞM s * (1 + σ s) ^ (-d)) := by
          rw [ENNReal.ofReal_mul hK]
          ring
  intro s hs
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hI]
  exact key s hs

/-- The four analytic estimates give the constant-term bound on their common
representative set, with no compact invariance or covering premise. -/
def ConstantTermRepresentativeEstimateStatement : Prop :=
  ∀ (G : Type u) [Group G] [MeasurableSpace G] (M U : Subgroup G)
    (ν : Measure U) (δ : M →* ℝ≥0ˣ) (Ξ σ : G → ℝ) (ΞM : M → ℝ)
    (S : Set M) (e eM : M → ℝ) (w : U → ℝ),
    (∀ g, 0 ≤ σ g) → (∀ m, 0 ≤ ΞM m) → (∀ m ∈ S, 0 ≤ e m) →
    (∀ u, 0 ≤ w u) → (∀ m ∈ S, e m * NNReal.sqrt (δ m) ≤ eM m) →
    UnipotentXiBound Ξ σ S e w → SigmaProductBound M U σ →
    XiLowerBound ΞM S eM → UnipotentWeightIntegrable ν w σ →
    ∀ d : ℝ, ∃ d' : ℝ, ∃ c : ℝ≥0, ∀ m ∈ S,
      (NNReal.sqrt (δ m) : ℝ≥0∞) *
        ∫⁻ u : U, ENNReal.ofReal
          (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-d')) ∂ν ≤
            c * ENNReal.ofReal (ΞM m * (1 + σ m) ^ (-d))

/-- The scalar representative estimate with arbitrary real target exponent. -/
theorem constantTermRepresentativeEstimate : ConstantTermRepresentativeEstimateStatement.{u} := by
  intro G _ _ M U ν δ Ξ σ ΞM S e eM w hσ hΞM he hw heM h44 h31 h11 h42
  exact constantTermRepresentativeEstimate_of_bounds hσ hΞM he hw heM h44 h31 h11 h42

end Langlands.HarishChandraSchwartz
