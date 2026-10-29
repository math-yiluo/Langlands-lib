import Langlands.HarmonicAnalysis.SchwartzBruhatValuationBoundsStatement
import Langlands.LocalField.Normalization.Continuity

/-!
# Valuation cutoffs and uniform bounds for scalar Schwartz–Bruhat functions: proof

The normalized absolute value is continuous for the supplied topology, and every
neighbourhood of zero contains a normalized ball around zero. Compact support then
bounds the normalized absolute value on the support, and local constancy at zero
gives a ball on which the function equals its value at zero.
-/

namespace Langlands.PadicField.TopologicalData

open scoped Topology

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- Every neighbourhood of zero for the supplied topology contains a normalized ball
around zero. -/
theorem exists_normalizedAbs_ball_subset {s : Set F.Carrier}
    (hs : letI := T.topology; s ∈ 𝓝 (0 : F.Carrier)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : F.Carrier, T.normalizedAbs x < ε → x ∈ s := by
  let := T.topology
  obtain ⟨t, ⟨a, ε, hε, rfl⟩, h0, hts⟩ := T.normalizedAbs_balls_basis.mem_nhds_iff.mp hs
  refine ⟨ε, hε, fun x hx => hts ?_⟩
  have ha : T.normalizedAbs (-a) < ε := by simpa using h0
  show T.normalizedAbs (x - a) < ε
  rw [sub_eq_add_neg]
  exact (T.normalizedAbs_add_le_max x (-a)).trans_lt (max_lt hx ha)

end Langlands.PadicField.TopologicalData

namespace Langlands.HarmonicAnalysis

open scoped Topology

universe uF

/-- Every scalar Schwartz–Bruhat function on a supplied p-adic field is bounded,
vanishes on units of sufficiently negative order and equals its value at zero on
units of sufficiently large order. -/
theorem schwartzBruhatValuationBounds : SchwartzBruhatValuationBoundsStatement.{uF} := by
  intro p _ F T Φ
  let := T.topology
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  -- A uniform bound for `Φ`.
  obtain ⟨C₀, hC₀⟩ := Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  -- A bound for the normalized absolute value on the support of `Φ`.
  obtain ⟨M, hM⟩ := (Φ.hasCompactSupport : IsCompact (tsupport Φ)).exists_bound_of_continuousOn
    T.continuous_normalizedAbs.continuousOn
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hq
  -- A normalized ball around zero on which `Φ` equals `Φ 0`.
  have hfib : {x : F.Carrier | Φ x = Φ 0} ∈ 𝓝 (0 : F.Carrier) :=
    (Φ.locallyConstant.isOpen_fiber (Φ 0)).mem_nhds rfl
  obtain ⟨ε, hε, hball⟩ := T.exists_normalizedAbs_ball_subset hfib
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hq)
  refine ⟨-(n : ℤ), N, max C₀ 1, by omega, lt_max_of_lt_right one_pos,
    fun x => (hC₀ x).trans (le_max_left _ _), ?_, ?_⟩
  · intro a ha
    by_contra hne
    have h1 := hM _ (subset_tsupport _ hne)
    rw [Real.norm_of_nonneg (T.normalizedAbs_nonneg _),
      T.normalizedAbs_of_ne_zero a.ne_zero] at h1
    have h2 : (T.residueCardinality : ℝ) ^ (n : ℤ) ≤
        (T.residueCardinality : ℝ) ^ (-T.ord (a : F.Carrier)) :=
      zpow_le_zpow_right₀ hq.le (by omega)
    rw [zpow_natCast] at h2
    linarith
  · intro a ha
    apply hball
    rw [T.normalizedAbs_of_ne_zero a.ne_zero]
    calc (T.residueCardinality : ℝ) ^ (-T.ord (a : F.Carrier))
        ≤ (T.residueCardinality : ℝ) ^ (-(N : ℤ)) := zpow_le_zpow_right₀ hq.le (by omega)
      _ = ((T.residueCardinality : ℝ)⁻¹) ^ N := by rw [zpow_neg, zpow_natCast, inv_pow]
      _ < ε := hN

end Langlands.HarmonicAnalysis
