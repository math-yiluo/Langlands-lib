import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Langlands.Galois.Local.AbsoluteDefinitions
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Linear bounds for continuous additive maps commuting with one scalar

A continuous additive endomorphism of a normed space over a nontrivially normed field which
commutes with multiplication by one scalar `c` of norm `> 1` is bounded: `‖f x‖ ≤ C ‖x‖`. For
nonarchimedean local fields `E` and `F`, with `E` an `F`-algebra carrying the `F`-module topology
and normed by its local norm, some element of `F` has norm `> 1` in `E`; this is the scalar used
to bound continuous `F`-linear maps in `Langlands.BaseChange.TwistedLocalDescent.ChartLinear`.
See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open Filter Topology

universe u v

section Bound

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem map_zpow_smul_of_map_smul (f : X →+ X) {c : 𝕜} (hc : c ≠ 0)
    (hfc : ∀ x, f (c • x) = c • f x) (k : ℤ) (x : X) : f (c ^ k • x) = c ^ k • f x := by
  have hnat : ∀ (a : 𝕜), (∀ x, f (a • x) = a • f x) → ∀ (k : ℕ) (x : X),
      f (a ^ k • x) = a ^ k • f x := by
    intro a ha k
    induction k with
    | zero => simp
    | succ k ih =>
      intro x
      rw [pow_succ', mul_smul, ha, ih, mul_smul]
  have hinv : ∀ x, f (c⁻¹ • x) = c⁻¹ • f x := by
    intro x
    have h1 : f x = c • f (c⁻¹ • x) := by
      rw [← hfc, smul_inv_smul₀ hc]
    rw [h1, inv_smul_smul₀ hc]
  rcases k with k | k
  · simpa using hnat c hfc k x
  · rw [zpow_negSucc, ← inv_pow]
    exact hnat c⁻¹ hinv (k + 1) x

/-- **A continuous additive map commuting with a scalar of norm `> 1` is bounded.** -/
theorem exists_norm_le_of_continuous_of_map_smul (f : X →+ X) (hf : Continuous f) {c : 𝕜}
    (hc : 1 < ‖c‖) (hfc : ∀ x, f (c • x) = c • f x) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * ‖x‖ := by
  have hc0 : c ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hc)
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuous_iff.mp hf 0 1 zero_lt_one
  refine ⟨δ⁻¹ * ‖c‖, by positivity, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨k, hk0, hkx, -, hkn⟩ := rescale_to_shell_zpow hc hδ hx
  have h1 : ‖f (c ^ k • x)‖ < 1 := by
    have := hδf (c ^ k • x) (by rwa [dist_zero_right])
    rwa [map_zero, dist_zero_right] at this
  rw [map_zpow_smul_of_map_smul f hc0 hfc, norm_smul] at h1
  have hpos : 0 < ‖c ^ k‖ := norm_pos_iff.mpr hk0
  have h2 : ‖f x‖ < ‖c ^ k‖⁻¹ := by
    rw [← one_div, lt_div_iff₀' hpos]
    exact h1
  exact h2.le.trans hkn

end Bound

section LocalField

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E]

/-- Some element of `F` has norm `> 1` in `E`. -/
theorem exists_one_lt_norm_algebraMap :
    letI := LocalGalois.localNormedField E
    ∃ a : F, 1 < ‖algebraMap F E a‖ := by
  letI := LocalGalois.localNormedField F
  letI := LocalGalois.localNormedField E
  obtain ⟨b, hb0, hb1⟩ := NormedField.exists_norm_lt_one F
  have hb : b ≠ 0 := norm_pos_iff.mp hb0
  have hcont : Continuous (algebraMap F E) := continuous_algebraMap F E
  have hlim : Tendsto (fun k : ℕ => b ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hb1
  have hlim' : Tendsto (fun k : ℕ => (algebraMap F E b) ^ k) atTop (𝓝 0) := by
    have := (hcont.tendsto 0).comp hlim
    rw [map_zero] at this
    refine this.congr fun k => ?_
    simp [map_pow]
  have hnorm : ‖algebraMap F E b‖ < 1 := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp hlim'
  have hne : algebraMap F E b ≠ 0 := (map_ne_zero (algebraMap F E)).mpr hb
  refine ⟨b⁻¹, ?_⟩
  rw [map_inv₀, norm_inv]
  exact one_lt_inv₀ (norm_pos_iff.mpr hne) |>.mpr hnorm

end LocalField

end Langlands.BaseChange.TwistedLocalDescent
