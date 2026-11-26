import Langlands.BaseChange.TwistedCharacter.CompactOpenHaarChart
import Mathlib.Topology.Algebra.Group.Units

/-! # Haar measure on a compact open subgroup in additive coordinates -/

noncomputable section

namespace Langlands.Analysis

open Function MeasureTheory Measure Topology Set Langlands.BaseChange
open Langlands.HarishChandraSchwartz
open scoped ENNReal NNReal

universe u v

section Restriction

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- The restriction of a left Haar measure to a compact open subgroup is its mass times the
pushforward of the normalized Haar measure of the subgroup. -/
theorem restrict_eq_smul_map_normalizedHaar (μ : Measure G) [μ.IsHaarMeasure]
    (K : Subgroup G) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
    μ.restrict K = μ K • Measure.map Subtype.val (normalizedHaar K) := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hmeas : MeasurableSet (K : Set G) := hKo.measurableSet
  have hemb : MeasurableEmbedding (Subtype.val : K → G) := MeasurableEmbedding.subtype_coe hmeas
  let ρ : Measure K := μ.comap Subtype.val
  have hρuniv : ρ univ = μ K := by
    change μ.comap Subtype.val univ = μ K
    rw [hemb.comap_apply, image_univ, Subtype.range_coe]
  have : IsFiniteMeasure ρ := ⟨by rw [hρuniv]; exact hKc.measure_lt_top⟩
  have : ρ.IsMulLeftInvariant := by
    constructor
    intro h
    ext1 s hs
    rw [map_apply (measurable_const_mul h) hs]
    change μ.comap Subtype.val _ = μ.comap Subtype.val s
    rw [hemb.comap_apply, hemb.comap_apply]
    have himg : Subtype.val '' ((h * ·) ⁻¹' s) = (h.val * ·) ⁻¹' (Subtype.val '' s) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨h * y, hy, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have hx : x ∈ K := by
          have : h.val * x ∈ K := by
            rw [← show (y : G) = h.val * x from hyx]
            exact y.property
          simpa using K.mul_mem (K.inv_mem h.property) this
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        change h * ⟨x, hx⟩ ∈ s
        have : h * ⟨x, hx⟩ = y := Subtype.ext hyx.symm
        rw [this]
        exact hy
    rw [himg, measure_preimage_mul]
  have : SecondCountableTopology K := IsInducing.subtypeVal.secondCountableTopology
  have hhaar : ρ = ρ univ • normalizedHaar K := by
    simpa only [TopologicalSpace.PositiveCompacts.coe_top, normalizedHaar] using
      haarMeasure_unique ρ ⊤
  calc
    μ.restrict K = Measure.map Subtype.val ρ := by
      rw [show ρ = μ.comap Subtype.val from rfl, hemb.map_comap, Subtype.range_coe_subtype]
      rfl
    _ = μ K • Measure.map Subtype.val (normalizedHaar K) := by
      rw [hhaar, Measure.map_smul, hρuniv]
      exact continuous_subtype_val.measurable.aemeasurable

end Restriction

section Units

variable {R : Type v} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
  [MeasurableSpace R] [BorelSpace R]
  [MeasurableSpace Rˣ] [BorelSpace Rˣ]

/-- For a compact open subgroup `K` of the units of a ring whose value map is an open
embedding, the value map carries Haar measure restricted to `K` to a multiple of additive
Haar measure restricted to the image of `K`. -/
theorem map_val_restrict_compactOpen (hval : IsOpenEmbedding (Units.val : Rˣ → R))
    (μ : Measure Rˣ) [μ.IsHaarMeasure] (νR : Measure R) [νR.IsAddHaarMeasure]
    (K : Subgroup Rˣ) (hKc : IsCompact (K : Set Rˣ)) (hKo : IsOpen (K : Set Rˣ)) :
    Measure.map Units.val (μ.restrict K) =
      (μ K * (νR (Units.val '' (K : Set Rˣ)))⁻¹) • νR.restrict (Units.val '' (K : Set Rˣ)) := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have : SecondCountableTopology Rˣ := hval.isEmbedding.secondCountableTopology
  let i : K →* Rˣ := K.subtype
  have hi : IsOpenEmbedding (fun h : K => (i h : R)) :=
    hval.comp hKo.isOpenEmbedding_subtypeVal
  have hrange : range (fun h : K => (i h : R)) = Units.val '' (K : Set Rˣ) := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h.val, h.property, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have h1 := restrict_eq_smul_map_normalizedHaar μ K hKc hKo
  have h2 := map_normalizedHaar_eq_restrict_of_units i hi νR
  rw [hrange] at h2
  rw [h1, Measure.map_smul, Measure.map_map Units.continuous_val.measurable
    continuous_subtype_val.measurable]
  change μ K • Measure.map (fun h : K => (i h : R)) (normalizedHaar K) = _
  rw [h2, smul_smul]
  exact Units.continuous_val.measurable.aemeasurable

end Units

end Langlands.Analysis
