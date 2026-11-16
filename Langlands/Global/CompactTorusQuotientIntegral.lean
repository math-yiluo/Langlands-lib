import Langlands.Analysis.Local.CompactFactorThickening
import Langlands.Global.LeftCosetSubgroupSlice
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.IwasawaIntegration

/-! # A compact torus criterion for fundamental-domain integrals -/

noncomputable section

namespace Langlands.Global.LeftCosetSpace

open MeasureTheory Measure Set Topology TopologicalSpace
open Langlands.HarishChandraSchwartz Langlands.CompactFactorization
open scoped ENNReal NNReal

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {M U : Subgroup G}

/-- The modularly weighted torus integrals of `f` are bounded uniformly as the
right translate ranges over each compact subset of the ambient group. -/
def HasCompactTorusBound (μM : Measure M) (δ : M →* ℝ≥0ˣ)
    (f : G → ℝ≥0∞) : Prop :=
  ∀ C : Set G, IsCompact C → ∃ B : ℝ≥0∞, B < ⊤ ∧
    ∀ c ∈ C, ∫⁻ m, (((δ m : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
      f ((m : G) * c) ∂μM ≤ B

/-- An ambient transversal, evaluated in `m u` coordinates, integrates on every
unipotent fiber to the same covolume, with the inverse conjugation modulus. -/
theorem lintegral_leviUnipotent_indicator_eq
    [MeasurableMul₂ G]
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (Γ : Subgroup G) (hΓU : Γ ≤ U) [Countable (Γ.comap U.subtype)]
    {s : Set G} (hs : MeasurableSet s)
    (huniq : ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ s)
    (μM : Measure M) [SFinite μM] (μU : Measure U) [SFinite μU]
    [μU.IsMulLeftInvariant] {t : Set U}
    (ht : IsFundamentalDomain (Γ.comap U.subtype) t μU) (htfinite : μU t < ⊤)
    (δ : M →* ℝ≥0ˣ) (hν : IsConjModulus hMU μU δ)
    (f : G → ℝ≥0∞) (hfm : Measurable f)
    (hf : ∀ (u : U) (g : G), f ((u : G) * g) = f g) (c : G) :
    ∫⁻ x : M × U, s.indicator f (leviUnipotentMul x * c) ∂(μM.prod μU) =
      μU t * ∫⁻ m, (((δ m : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
        f ((m : G) * c) ∂μM := by
  have hmeas : Measurable fun x : M × U =>
      s.indicator f (leviUnipotentMul x * c) :=
    (hfm.indicator hs).comp
      (((measurable_subtype_coe.comp measurable_fst).mul
        (measurable_subtype_coe.comp measurable_snd)).mul_const c)
  rw [lintegral_prod _ hmeas.aemeasurable]
  have hinner (m : M) :
      ∫⁻ u : U, s.indicator f (leviUnipotentMul (m, u) * c) ∂μU =
        (((δ m : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) * (μU t * f ((m : G) * c)) := by
    have h := hν.lintegral_comp m
      (fun v : U => s.indicator f ((v : G) * ((m : G) * c)))
    rw [lintegral_subgroupSlice_indicator Γ U hΓU hs huniq μU ht f hf] at h
    rw [← h]
    apply lintegral_congr
    intro u
    congr 1
    simp only [leviUnipotentMul, conjUnipotent]
    group
  simp_rw [hinner, ← mul_left_comm (μU t)]
  exact lintegral_const_mul' (μU t) _ htfinite.ne

/-- With `G = M U K`, compact `K`, finite subgroup covolume and the conjugation
modulus, compact-uniform weighted torus bounds imply a finite integral over the
given ambient fundamental domain. -/
theorem lintegral_fundamentalDomain_lt_top_of_compactTorusBound
    [SecondCountableTopology G] [T2Space G] [LocallyCompactSpace G]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (μM : Measure M) [SFinite μM] [μM.IsMulLeftInvariant] [IsOpenPosMeasure μM]
    (μU : Measure U) [SFinite μU] [μU.IsMulLeftInvariant] [IsOpenPosMeasure μU]
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (K Γ : Subgroup G) (hK : IsCompact (K : Set G)) (hΓU : Γ ≤ U)
    [Countable (Γ.comap U.subtype)]
    (hfac : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
    {s : Set G} (hs : MeasurableSet s)
    (huniq : ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ s)
    {t : Set U} (ht : IsFundamentalDomain (Γ.comap U.subtype) t μU)
    (htfinite : μU t < ⊤)
    (δ : M →* ℝ≥0ˣ) (hν : IsConjModulus hMU μU δ)
    (f : G → ℝ≥0∞) (hfm : Measurable f)
    (hf : ∀ (u : U) (g : G), f ((u : G) * g) = f g)
    (hbound : HasCompactTorusBound μM δ f) :
    ∫⁻ g in s, f g ∂μ < ⊤ := by
  let : SecondCountableTopology M :=
    secondCountableTopology_induced _ G (fun m : M => (m : G))
  let : SecondCountableTopology U :=
    secondCountableTopology_induced _ G (fun u : U => (u : G))
  obtain ⟨C, hCc, hCn, hCK⟩ :=
    exists_compact_rightSubgroupInvariant_neighborhood K hK
  obtain ⟨B, hB, hCB⟩ := hbound C hCc
  have hι : Measurable (leviUnipotentMul (M := M) (U := U)) :=
    continuous_leviUnipotentMul.measurable
  have hmass : (μM.prod μU) {x : M × U | (leviUnipotentMul x)⁻¹ ∈ C} ≠ 0 := by
    apply ne_of_gt
    apply Measure.measure_pos_of_mem_nhds (μM.prod μU) (x := ((1 : M), (1 : U)))
    have hc : Continuous fun x : M × U => (leviUnipotentMul x)⁻¹ :=
      continuous_leviUnipotentMul.inv
    exact hc.continuousAt.preimage_mem_nhds (by simpa [leviUnipotentMul] using hCn)
  rw [← lintegral_indicator hs]
  apply lintegral_lt_top_of_rightInvariant_majorant μ K C hCc.measurableSet hCK
    hCc.measure_lt_top (μM.prod μU) leviUnipotentMul hι
    (fun g => by
      obtain ⟨m, u, k, hk, rfl⟩ := hfac g
      exact ⟨(m, u), k, hk, rfl⟩)
    (fun x₀ => ⟨leviUnipotentShift hMU x₀,
      measurePreserving_leviUnipotentShift hMU x₀,
      fun x => leviUnipotentMul_shift hMU x₀ x⟩)
    hmass (s.indicator f) (hfm.indicator hs) (μU t * B)
    (ENNReal.mul_lt_top htfinite hB)
  intro c hc
  rw [lintegral_leviUnipotent_indicator_eq hMU Γ hΓU hs huniq μM μU ht
    htfinite δ hν f hfm hf]
  exact mul_le_mul_right (hCB c hc) _

end Langlands.Global.LeftCosetSpace
