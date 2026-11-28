import Langlands.HarmonicAnalysis.Distribution.LocallyIntegrablePushforward
import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentParabolicAbsoluteContinuity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-! # Locally integrable densities under idempotent parabolic conjugation

A locally integrable function of the Levi coordinate has a locally integrable weighted
pushforward density under parabolic conjugation over a compact open unit chart.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer

open Function MeasureTheory Set

universe u v

variable (F : Type u) [NontriviallyNormedField F] [ProperSpace F]
  {A : Type v} [NormedRing A] [NormedAlgebra F A] [FiniteDimensional F A]
  [MeasurableSpace A] [BorelSpace A] (e : A)

local notation "Levi" => Subalgebra.centralizer F (Set.singleton e)
local notation "Upper" => offDiagonalCorner F e
local notation "Coordinates" => A × (Levi × Upper)

/-- With the first coordinate restricted to a compact open unit chart, the pushforward
under parabolic conjugation of a locally integrable Levi weight has a locally integrable
density. -/
def IdempotentParabolicDensityStatement [IsUltrametricDist A] : Prop :=
  IsIdempotentElem e →
    ∀ (C : Set A), IsCompact C → IsOpen C → (∀ a ∈ C, IsUnit a) →
      ∀ (μA : Measure A) [μA.IsAddHaarMeasure]
        (μM : Measure Levi) [μM.IsAddHaarMeasure]
        (μU : Measure Upper) [μU.IsAddHaarMeasure]
        (ν : Measure A) [ν.IsAddHaarMeasure] (θ : Levi → ℂ),
        LocallyIntegrable θ μM →
        ∃ r : A → ℂ, LocallyIntegrable r ν ∧
          ∀ f : SchwartzBruhat A,
            (∫ x, r x * f x ∂ν) =
              ∫ p : Coordinates, θ p.2.1 * f (parabolicChartConjugation F e C p)
                ∂((μA.restrict C).prod (μM.prod μU))

theorem idempotentParabolicDensity [IsUltrametricDist A] :
    IdempotentParabolicDensityStatement F e := by
  intro he C hCc hCo hUnits μA _ μM _ μU _ ν _ θ hθ
  have : ProperSpace A := FiniteDimensional.proper F A
  have : ProperSpace Levi := FiniteDimensional.proper F Levi
  have : ProperSpace Upper := FiniteDimensional.proper F Upper
  let Φ := parabolicChartConjugation F e C
  obtain ⟨hΦ, hAC⟩ := idempotentParabolicAbsoluteContinuity F e he C ⟨hCc.isClosed, hCo⟩
    hUnits μA μM μU ν
  let d : A →L[F] Levi := ((diagonalProjection F e).codRestrict (Levi).toSubmodule
    (fun x => (mem_centralizer_singleton_iff F).2 (commute_diagonalProjection he x))).toContinuousLinearMap
  let u : A →L[F] Upper := (cornerProjection F e).rangeRestrict.toContinuousLinearMap
  obtain ⟨_, h₂, h₃, h₄, h₅, h₆, _, _⟩ := idempotent_mul_rules he
  have hd (y : Levi) (z : Upper) : d ((y : A) + z) = y := by
    apply Subtype.ext
    change diagonalProjection F e ((y : A) + z) = y
    rw [map_add, diagonalProjection_of_commute he ((mem_centralizer_singleton_iff F).1 y.property)]
    obtain ⟨x, hx⟩ := z.property
    rw [← hx]
    simp only [diagonalProjection_apply, cornerProjection_apply, mul_assoc, h₂, mul_zero,
      h₆, zero_mul, add_zero]
  have hu (y : Levi) (z : Upper) : u ((y : A) + z) = z := by
    apply Subtype.ext
    change cornerProjection F e ((y : A) + z) = z
    have hy : cornerProjection F e (y : A) = 0 := by
      rw [cornerProjection_apply, (mem_centralizer_singleton_iff F).1 y.property, mul_assoc,
        h₃, mul_zero]
    rw [map_add, hy, zero_add]
    obtain ⟨x, hx⟩ := z.property
    rw [← hx]
    simp only [cornerProjection_apply, mul_assoc, h₄, h₅]
  apply locallyIntegrablePushforward Coordinates A _ _ Φ (fun p => θ p.2.1) hΦ.measurable hAC
  intro K hK
  let ψ : A × A → A := fun q => Ring.inverse q.1 * q.2 * q.1
  have hψ : ContinuousOn ψ (C ×ˢ K) := by
    intro q hq
    obtain ⟨g, hg⟩ := hUnits q.1 hq.1
    have hInv : ContinuousAt (Ring.inverse : A → A) q.1 := by
      rw [← hg]
      exact (hasStrictFDerivAt_ringInverse (𝕜 := F) g).continuousAt
    exact (((hInv.comp continuous_fst.continuousAt).mul continuous_snd.continuousAt).mul
      continuous_fst.continuousAt).continuousWithinAt
  let S := ψ '' (C ×ˢ K)
  have hS : IsCompact S := (hCc.prod hK).image_of_continuousOn hψ
  let B : Set Levi := d '' S
  let D : Set Upper := u '' S
  have hB : IsCompact B := hS.image d.continuous
  have hD : IsCompact D := hS.image u.continuous
  have : IsFiniteMeasure (μA.restrict C) := isFiniteMeasure_restrict.2 hCc.measure_ne_top
  have : IsFiniteMeasure (μU.restrict D) := isFiniteMeasure_restrict.2 hD.measure_ne_top
  have hθB : IntegrableOn θ B μM :=
    (hθ.locallyIntegrableOn B).integrableOn_isCompact hB
  have hbox : IntegrableOn (fun p : Coordinates => θ p.2.1) (C ×ˢ (B ×ˢ D))
      (μA.prod (μM.prod μU)) := by
    rw [IntegrableOn, ← Measure.prod_restrict, ← Measure.prod_restrict]
    exact (hθB.comp_fst (μU.restrict D)).comp_snd (μA.restrict C)
  rw [IntegrableOn, Measure.restrict_prod_eq_prod_univ,
    Measure.restrict_restrict (hΦ.measurable hK.isClosed.measurableSet), Set.prod_univ]
  refine hbox.mono_set ?_
  intro p hp
  have hpC : p.1 ∈ C := hp.2
  have hpK : Φ p ∈ K := hp.1
  have hpS : (p.2.1 : A) + p.2.2 ∈ S := by
    refine ⟨(p.1, Φ p), ⟨hpC, hpK⟩, ?_⟩
    obtain ⟨g, hg⟩ := hUnits p.1 hpC
    change Ring.inverse p.1 * Φ p * p.1 = _
    rw [show Φ p = parabolicConjugation F e p from parabolicChartConjugation_of_mem F e hpC]
    simp only [parabolicConjugation, ← hg, Ring.inverse_unit]
    calc
      _ = (((g⁻¹ : Aˣ) : A) * (g : A)) * ((p.2.1 : A) + p.2.2) *
          (((g⁻¹ : Aˣ) : A) * (g : A)) := by noncomm_ring
      _ = _ := by rw [Units.inv_mul, one_mul, mul_one]
  exact ⟨hpC, ⟨_, hpS, hd p.2.1 p.2.2⟩, ⟨_, hpS, hu p.2.1 p.2.2⟩⟩

end Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer
