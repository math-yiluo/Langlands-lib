import Langlands.HarmonicAnalysis.Distribution.IntegrablePushforward
import Langlands.HarmonicAnalysis.Distribution.LocallyIntegrableGluing

/-! # Pushforward of a weight integrable over compact preimages -/

noncomputable section

namespace Langlands.HarmonicAnalysis

open Filter Function MeasureTheory Set
open scoped Topology

/-- A complex weight integrable over compact preimages has a locally integrable
pushforward density if the underlying pushforward is absolutely continuous. -/
def LocallyIntegrablePushforwardStatement.{u, v} : Prop :=
  ∀ (X : Type u) [MeasurableSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    [TotallyDisconnectedSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite ν]
    (p : X → Y) (f : X → ℂ), Measurable p → μ.map p ≪ ν →
    (∀ K : Set Y, IsCompact K → IntegrableOn f (p ⁻¹' K) μ) →
    ∃ r : Y → ℂ, LocallyIntegrable r ν ∧
      ∀ g : SchwartzBruhat Y, (∫ y, r y * g y ∂ν) = ∫ x, f x * g (p x) ∂μ

theorem locallyIntegrablePushforward : LocallyIntegrablePushforwardStatement.{u, v} := by
  classical
  intro X _ Y _ _ _ _ _ _ _ μ ν _ p f hp hμν hf
  have hbounded (g : SchwartzBruhat Y) : ∃ C : ℝ, ∀ y, ‖g y‖ ≤ C :=
    g.continuous.bounded_above_of_compact_support g.hasCompactSupport
  have hzero (g : SchwartzBruhat Y) {K : Set Y} (hK : support (g : Y → ℂ) ⊆ K) :
      ∀ x ∉ p ⁻¹' K, f x * g (p x) = 0 := by
    intro x hx
    have hg : g (p x) = 0 := notMem_support.mp (fun h => hx (hK h))
    rw [hg, mul_zero]
  have htest (g : SchwartzBruhat Y) : Integrable (fun x => f x * g (p x)) μ := by
    let K := tsupport (g : Y → ℂ)
    have hmeas : MeasurableSet (p ⁻¹' K) := hp isClosed_closure.measurableSet
    obtain ⟨C, hC⟩ := hbounded g
    have hint : IntegrableOn (fun x => f x * g (p x)) (p ⁻¹' K) μ :=
      (hf K g.hasCompactSupport).mul_bdd (g.continuous.measurable.comp hp).aestronglyMeasurable
        (Eventually.of_forall fun x => hC (p x))
    have hind := (integrable_indicator_iff hmeas).2 hint
    convert hind using 1
    ext x
    by_cases hx : x ∈ p ⁻¹' K
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hzero g (subset_tsupport _) x hx]
  let D : Distribution Y :=
    { toFun := fun g => ∫ x, f x * g (p x) ∂μ
      map_add' := fun g h => by
        change (∫ x, f x * (g (p x) + h (p x)) ∂μ) = _
        simp_rw [mul_add]
        exact integral_add (htest g) (htest h)
      map_smul' := fun c g => by
        change (∫ x, f x * (c * g (p x)) ∂μ) = c * ∫ x, f x * g (p x) ∂μ
        simp_rw [← mul_assoc, mul_comm (f _) c, mul_assoc]
        exact integral_const_mul c _ }
  have hlocal (y : Y) : ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ ∃ r : Y → ℂ,
      (∀ _ : Unit, LocallyIntegrableOn r U ν ∧
        ∀ g : SchwartzBruhat Y, support (g : Y → ℂ) ⊆ U →
          D g = ∫ z, g z * r z ∂ν) ∧
      ∀ z ∈ U ∩ (∅ : Set Y), ∀ᶠ w in 𝓝 z, r w = r z := by
    obtain ⟨K, hK, hyK⟩ := exists_compact_mem_nhds y
    let μK := μ.restrict (p ⁻¹' K)
    have hAC : μK.map p ≪ ν :=
      (Measure.absolutelyContinuous_of_le
        (Measure.map_mono_of_aemeasurable Measure.restrict_le_self hp.aemeasurable)).trans hμν
    obtain ⟨r, hr, hrTest⟩ := integrablePushforward hp hAC f (hf K hK)
    refine ⟨interior K, isOpen_interior, mem_interior_iff_mem_nhds.mpr hyK, r,
      fun _ => ⟨hr.locallyIntegrable.locallyIntegrableOn _, fun g hg => ?_⟩,
      fun z hz => (Set.notMem_empty z hz.2).elim⟩
    change (∫ x, f x * g (p x) ∂μ) = _
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (hzero g (hg.trans interior_subset)), ← hrTest g g.continuous.measurable (hbounded g)]
    simp_rw [mul_comm]
  obtain ⟨r, hr, _⟩ := Distribution.exists_locallyIntegrableDensity_of_locally Y
    (fun _ : Unit => ν) (fun _ : Unit => D) ∅ hlocal
  refine ⟨r, (hr ()).1, fun g => ?_⟩
  change (∫ y, r y * g y ∂ν) = D g
  simpa only [mul_comm] using ((hr ()).2 g).symm

end Langlands.HarmonicAnalysis
