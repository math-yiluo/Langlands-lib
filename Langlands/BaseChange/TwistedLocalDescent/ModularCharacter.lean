import Langlands.Analysis.Local.ModularCompactAverage
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # The modular character of a group with a compact open subgroup

For a second countable locally compact group `H`, right translation by `q` multiplies a left Haar
measure by the modular character `Δ(q)`. The modular character is trivial on every compact open
subgroup; hence, when such a subgroup exists, it is locally constant, in particular continuous,
and invariant under every measurable endomorphism preserving the Haar measure. See the paired
Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open MeasureTheory Measure Set Topology
open scoped ENNReal NNReal

universe u

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- Right translation scales a left Haar measure by the modular character. -/
theorem map_mul_right_eq_modularCharacter_smul (μ : Measure H) [μ.IsHaarMeasure] (q : H) :
    μ.map (· * q) = (modularCharacter q : ℝ≥0∞) • μ := by
  have h := isMulLeftInvariant_eq_smul (μ.map (· * q)) μ
  rw [h, ← modularCharacterFun_eq_haarScalarFactor μ q]
  rfl

/-- With a compact open subgroup, the modular character is locally constant, hence continuous. -/
theorem continuous_modularCharacter (μ : Measure H) [μ.IsHaarMeasure] (K : Subgroup H)
    (hKo : IsOpen (K : Set H)) (hKc : IsCompact (K : Set H)) :
    Continuous (fun h : H => (modularCharacter h : ℝ≥0)) := by
  refine continuous_iff_continuousAt.mpr fun g => ?_
  have hnhds : (fun x => g * x) '' (K : Set H) ∈ 𝓝 g := by
    have : IsOpen ((fun x => g * x) '' (K : Set H)) := (isOpenMap_mul_left g) _ hKo
    exact this.mem_nhds ⟨1, K.one_mem, mul_one g⟩
  refine (continuousAt_const (y := (modularCharacter g : ℝ≥0))).congr ?_
  filter_upwards [hnhds] with x hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [map_mul, ModularCompactAverage.modularCharacter_eq_one_of_mem K hKo hKc hk, mul_one]

/-- When a compact open subgroup exists, the modular character is invariant under a measurable
endomorphism preserving the Haar measure. -/
theorem modularCharacter_map_eq (μ : Measure H) [μ.IsHaarMeasure] (θ : H →* H)
    (hθ : Measurable θ) (hμθ : μ.map θ = μ) (K : Subgroup H) (hKo : IsOpen (K : Set H))
    (hKc : IsCompact (K : Set H)) (h : H) :
    modularCharacter (θ h) = modularCharacter h := by
  have h1 : μ.map (· * θ h) = (modularCharacter h : ℝ≥0∞) • μ := by
    calc μ.map (· * θ h) = (μ.map θ).map (· * θ h) := by rw [hμθ]
      _ = (μ.map (· * h)).map θ := by
        rw [Measure.map_map (measurable_mul_const _) hθ,
          Measure.map_map hθ (measurable_mul_const _)]
        congr 1
        funext x
        simp [map_mul]
      _ = (modularCharacter h : ℝ≥0∞) • μ := by
        rw [map_mul_right_eq_modularCharacter_smul μ h, Measure.map_smul, hμθ]
        exact hθ.aemeasurable
  rw [map_mul_right_eq_modularCharacter_smul μ (θ h)] at h1
  have h2 := congrArg (fun ν : Measure H => ν K) h1
  simp only [Measure.smul_apply, smul_eq_mul] at h2
  have hpos : μ K ≠ 0 := (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have hfin : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  exact_mod_cast (ENNReal.mul_left_inj hpos hfin).mp h2

end Langlands.BaseChange.TwistedLocalDescent
