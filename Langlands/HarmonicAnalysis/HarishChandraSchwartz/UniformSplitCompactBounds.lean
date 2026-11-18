import Langlands.HarmonicAnalysis.HarishChandraSchwartz.UniformExponentAnnihilators

/-! # Compact bounds for actual positive parts from full-family compact bounds -/

noncomputable section

namespace Langlands.HarishChandraSchwartz

section Continuity

variable {κ M Y : Type*} [TopologicalSpace κ] [Group M] [TopologicalSpace M]
  [IsTopologicalGroup M] [TopologicalSpace Y]

/-- Pointwise parameter continuity becomes joint continuity when a common open subgroup
fixes every member of the family under right translation. -/
theorem continuous_uncurry_of_uniform_right_invariance
    {F : κ → M → Y} {U : Subgroup M} (hU : IsOpen (U : Set M))
    (hF : ∀ g, Continuous (fun ω => F ω g))
    (hinv : ∀ ω g k, k ∈ U → F ω (g * k) = F ω g) :
    Continuous (Function.uncurry F) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨ω, g⟩
  have hc : ContinuousAt (fun p : κ × M => F p.1 g) (ω, g) :=
    (hF g).continuousAt.comp continuous_fst.continuousAt
  apply hc.congr
  have hmem : ∀ᶠ p : κ × M in nhds (ω, g), g⁻¹ * p.2 ∈ U :=
    (hU.preimage (continuous_const.mul continuous_snd)).mem_nhds (by simp)
  filter_upwards [hmem] with p hp
  change F p.1 g = F p.1 p.2
  simpa only [mul_inv_cancel_left] using (hinv p.1 g (g⁻¹ * p.2) hp).symm

end Continuity

section CompactBounds

variable {κ M : Type*} [TopologicalSpace M]

/-- A function family is bounded by a common positive multiple of a weight on each compact
set, with that multiple independent of the family parameter. -/
def HasUniformWeightedCompactBounds (F : κ → M → ℂ) (B : M → ℝ) : Prop :=
  ∀ Q : Set M, IsCompact Q → ∃ C > 0, ∀ ω g, g ∈ Q → ‖F ω g‖ ≤ C * B g

/-- Compact bounds pull back along a continuous map, in particular an actual subgroup
inclusion. The splitting operation is performed before this pullback. -/
theorem HasUniformWeightedCompactBounds.comp {F : κ → M → ℂ} {B : M → ℝ}
    (h : HasUniformWeightedCompactBounds F B) {L : Type*} [TopologicalSpace L]
    (f : L → M) (hf : Continuous f) :
    HasUniformWeightedCompactBounds (fun ω => F ω ∘ f) (B ∘ f) := by
  intro Q hQ
  obtain ⟨C, hC, hb⟩ := h (f '' Q) (hQ.image hf)
  exact ⟨C, hC, fun ω g hg => hb ω (f g) ⟨g, hg, rfl⟩⟩

/-- A jointly continuous family indexed by a compact space has weighted compact bounds
against every continuous, everywhere-positive weight. -/
theorem hasUniformWeightedCompactBounds_of_continuous
    [TopologicalSpace κ] [CompactSpace κ] {F : κ → M → ℂ} {B : M → ℝ}
    (hF : Continuous (Function.uncurry F)) (hB : Continuous B) (hBpos : ∀ g, 0 < B g) :
    HasUniformWeightedCompactBounds F B := by
  intro Q hQ
  let f : κ × M → ℝ := fun p => ‖F p.1 p.2‖ / B p.2
  have hf : Continuous f :=
    hF.norm.div (hB.comp continuous_snd) fun p => (hBpos p.2).ne'
  obtain ⟨b, hb⟩ := (isCompact_univ.prod hQ).bddAbove_image hf.continuousOn
  refine ⟨max b 1, zero_lt_one.trans_le (le_max_right _ _), fun ω g hg => ?_⟩
  have hp : (ω, g) ∈ (Set.univ : Set κ) ×ˢ Q := ⟨Set.mem_univ _, hg⟩
  exact (div_le_iff₀ (hBpos g)).mp
    ((hb ⟨(ω, g), hp, rfl⟩).trans (le_max_left _ _))

variable [Group M] [IsTopologicalGroup M] {A : Type*} [CommGroup A]

/-- Uniform split annihilators transfer compact weighted bounds from the full functions
to their actual positive parts. Continuity of the positive parts is not a premise. -/
theorem HasUniformSplitAnnihilators.hasUniformWeightedCompactBounds_positivePart
    {j : A →* M} {a : A} {F : κ → M → ℂ} {B : M → ℝ}
    (hann : HasUniformSplitAnnihilators j a F)
    (hF : HasUniformWeightedCompactBounds F B)
    (hB : ∀ g, B (g * j a) = B g) :
    HasUniformWeightedCompactBounds (fun ω => positivePart j (F ω)) B := by
  obtain ⟨Nw, Np, θ, pw, pp, _, hθ, hpw, hpp, hNw, hNp, hrw, hrp, hannw, hannp⟩ := hann
  obtain ⟨Cw, hCw⟩ := exists_norm_le_sum_translates (j a) Nw Np hθ
  let K : ℕ := Np * (Nw - 1) + Np + 1
  have hK : 0 < K := by dsimp [K]; omega
  have hBa : ∀ (g : M) (n : ℕ), B (g * j a ^ n) = B g := by
    intro g n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, hB, ih]
  intro Q hQ
  let Q' : Set M := ⋃ n ∈ Finset.range K, (fun g : M => g * j a ^ n) '' Q
  have hQ' : IsCompact Q' :=
    (Finset.range K).isCompact_biUnion fun n _ => hQ.image (by fun_prop)
  obtain ⟨C, hC, hb⟩ := hF Q' hQ'
  have htranslate : ∀ g ∈ Q, ∀ n ∈ Finset.range K, g * j a ^ n ∈ Q' := by
    intro g hg n hn
    exact Set.mem_iUnion₂.mpr ⟨n, hn, ⟨g, hg, rfl⟩⟩
  have hsub : Q ⊆ Q' := by
    intro g hg
    simpa only [pow_zero, mul_one] using htranslate g hg 0 (Finset.mem_range.mpr hK)
  refine ⟨C * (1 + |Cw| * K), mul_pos hC (by positivity), fun ω g hg => ?_⟩
  have hw := hCw (pw ω) (pp ω) (hpw ω) (hpp ω) (hNw ω) (hNp ω) (hrw ω) (hrp ω)
    (F ω) (weakPart j (F ω)) (positivePart j (F ω))
    (weakPart_add_positivePart j (F ω)).symm (hannw ω) (hannp ω) g
  have hsum : ∑ n ∈ Finset.range K, ‖F ω (g * j a ^ n)‖ ≤ K * C * B g := by
    calc ∑ n ∈ Finset.range K, ‖F ω (g * j a ^ n)‖
        ≤ ∑ n ∈ Finset.range K, C * B g := by
          refine Finset.sum_le_sum fun n hn => ?_
          simpa only [hBa] using hb ω (g * j a ^ n) (htranslate g hg n hn)
      _ = K * C * B g := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  calc ‖positivePart j (F ω) g‖ ≤ ‖F ω g‖ + ‖weakPart j (F ω) g‖ := by
        exact norm_sub_le _ _
    _ ≤ C * B g + |Cw| * (K * C * B g) := by
        refine add_le_add (hb ω g (hsub hg)) (hw.trans ?_)
        exact mul_le_mul (le_abs_self Cw) hsum
          (Finset.sum_nonneg fun _ _ => norm_nonneg _) (abs_nonneg _)
    _ = C * (1 + |Cw| * K) * B g := by ring

end CompactBounds

end Langlands.HarishChandraSchwartz
