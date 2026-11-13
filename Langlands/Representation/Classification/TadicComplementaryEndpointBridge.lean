import Langlands.Representation.Classification.TadicComplementaryEndpointHelpers
import Langlands.Representation.Classification.TadicComplementarySeriesUnitarityProof
import Langlands.Representation.Unitary.CharacterLimitSubquotientsStatement
import Langlands.Group.GL.CountabilityProof
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Reduction of the complementary endpoint to the character-limit theorem

This module derives Tadić's complementary-series proposition
`ComplementarySeriesUnitarity` from the character-limit theorem
`UnitaryCharacterLimitSubquotientsStatement`, taken as a hypothesis. The
open-interval part is the Library's `complementaryProduct_unitarizableOnInterval`.
The end-point part approximates the end point from inside the interval and
applies the character-limit theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option linter.overlappingInstances false
set_option maxHeartbeats 1000000

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData HarmonicAnalysis MeasureTheory Filter
open scoped NNReal _root_.Topology

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem approachEndpoint {a : ℝ} (ha : 0 < a) :
    (∀ k : ℕ, a - a / ((k : ℝ) + 1) ∈ Set.Ioo (-a) a) ∧
    Tendsto (fun k : ℕ => a - a / ((k : ℝ) + 1)) atTop (𝓝 a) := by
  constructor
  · intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hfrac : 0 < a / ((k : ℝ) + 1) := div_pos ha hk
    have hle : a / ((k : ℝ) + 1) ≤ a := by
      exact (div_le_iff₀ hk).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
    constructor <;> linarith
  · have ht : Tendsto (fun k : ℕ => a / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [mul_one_div, mul_zero] using
        (tendsto_const_nhds (x := a)).mul
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [sub_zero] using (tendsto_const_nhds (x := a)).sub ht

/-- Given the all-constituent character-limit theorem, the endpoint
clause follows for every supplied regular left and right invariant Haar measure. -/
theorem complementaryEndpoint_of_characterLimit
    (hlimit : UnitaryCharacterLimitSubquotientsStatement.{uF, max uF uV})
    {n : ℕ} (hn : 0 < n)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (a : ℝ) (hAi : letI := T.topology; A.IsIrreducible)
    (hAu : letI := T.topology; IsUnitarizable A.representation)
    (ha : 0 < a)
    (hirr : letI := T.topology
      ∀ s ∈ Set.Ioo (-a) a, (complementaryProduct F T hn A s).IsIrreducible) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (2 * n)
    letI := T.generalLinearT2Space (2 * n)
    letI := T.generalLinearLocallyCompactSpace (2 * n)
    letI := T.generalLinearNonarchimedean (2 * n)
    letI := T.generalLinearSecondCountableTopology (2 * n)
    letI : MeasurableSpace (GeneralLinear (2 * n) F.Carrier) := borel _
    letI : BorelSpace (GeneralLinear (2 * n) F.Carrier) := ⟨rfl⟩
    ∀ (μ : Measure (GeneralLinear (2 * n) F.Carrier))
      [μ.IsHaarMeasure] [μ.Regular] [Measure.IsMulRightInvariant μ]
      (τ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (2 * n) F.Carrier)),
      τ.IsIrreducible →
      SmoothRep.IsSubquotient τ (complementaryProduct F T hn A a) →
      IsUnitarizable τ.representation := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (2 * n)
  letI := T.generalLinearT2Space (2 * n)
  letI := T.generalLinearLocallyCompactSpace (2 * n)
  letI := T.generalLinearNonarchimedean (2 * n)
  letI := T.generalLinearSecondCountableTopology (2 * n)
  letI : MeasurableSpace (GeneralLinear (2 * n) F.Carrier) := borel _
  letI : BorelSpace (GeneralLinear (2 * n) F.Carrier) := ⟨rfl⟩
  intro μ _ _ _ τ hτ hsub
  have hAa : IsAdmissible A.representation :=
    (CuspidalSupport.cuspidalEmbedding F T n A hAi).1
  let x : ℕ → ℝ := fun k => a - a / ((k : ℝ) + 1)
  obtain ⟨hx, hxt⟩ := approachEndpoint ha
  let π : ℕ → SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (2 * n) F.Carrier) :=
    fun k => complementaryProduct F T hn A (x k)
  let ρ := complementaryProduct F T hn A a
  have hπ (k : ℕ) : IsAdmissible (π k).representation :=
    complementaryProduct_admissible F T hn A hAa (x k)
  have hρ : IsAdmissible ρ.representation :=
    complementaryProduct_admissible F T hn A hAa a
  have hi (k : ℕ) : (π k).IsIrreducible := hirr (x k) (hx k)
  have hu (k : ℕ) : IsUnitarizable (π k).representation :=
    complementaryProduct_unitarizableOnInterval F T hn A a hAi hAu ha hirr (x k) (hx k)
  have hfl : ρ.HasFiniteLength := complementaryProduct_finiteLength F T hn A hAi a
  have hc (f : SchwartzBruhat (GeneralLinear (2 * n) F.Carrier)) :
      Tendsto (fun k => Character.distribution μ (π k).representation (hπ k) f)
        atTop (𝓝 (Character.distribution μ ρ.representation hρ f)) :=
    (continuous_complementaryProduct_distribution F T hn A hAa μ f).continuousAt.tendsto.comp hxt
  exact hlimit (GeneralLinear (2 * n) F.Carrier) μ π hπ ρ hρ hi hu hfl hc τ hτ hsub

/-- Existence of a regular bi-invariant Haar measure on every positive-rank
actual general linear group. -/
private theorem exists_generalLinear_biHaar (m : ℕ) (hm : 0 < m) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup m
    letI := T.generalLinearT2Space m
    letI := T.generalLinearLocallyCompactSpace m
    letI : MeasurableSpace (GeneralLinear m F.Carrier) := borel _
    letI : BorelSpace (GeneralLinear m F.Carrier) := ⟨rfl⟩
    ∃ μ : Measure (GeneralLinear m F.Carrier),
      μ.IsHaarMeasure ∧ μ.Regular ∧ Measure.IsMulRightInvariant μ := by
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := T.generalLinearTopologicalGroup (m + 1)
  letI := T.generalLinearT2Space (m + 1)
  letI := T.generalLinearLocallyCompactSpace (m + 1)
  letI : MeasurableSpace (GeneralLinear (m + 1) F.Carrier) := borel _
  letI : BorelSpace (GeneralLinear (m + 1) F.Carrier) := ⟨rfl⟩
  exact ⟨RankinSelberg.generalLinearHaar F.Carrier m, inferInstance,
    inferInstance, inferInstance⟩

/-- Reduction of `ComplementarySeriesUnitarity` to the all-constituent
character-limit theorem. -/
theorem complementarySeriesUnitarity_of_characterLimit
    (hlimit : UnitaryCharacterLimitSubquotientsStatement.{uF, max uF uV}) :
    ComplementarySeriesUnitarity.{uF, uV} F T := by
  letI := T.topology
  intro n hn A a hAi hAu ha hirr
  refine ⟨complementaryProduct_unitarizableOnInterval F T hn A a hAi hAu ha hirr, ?_⟩
  letI := T.generalLinearTopologicalGroup (2 * n)
  letI := T.generalLinearT2Space (2 * n)
  letI := T.generalLinearLocallyCompactSpace (2 * n)
  letI := T.generalLinearNonarchimedean (2 * n)
  letI := T.generalLinearSecondCountableTopology (2 * n)
  letI : MeasurableSpace (GeneralLinear (2 * n) F.Carrier) := borel _
  letI : BorelSpace (GeneralLinear (2 * n) F.Carrier) := ⟨rfl⟩
  obtain ⟨μ, hμ, hμreg, hμright⟩ :=
    exists_generalLinear_biHaar F T (2 * n) (by omega)
  letI := hμ
  letI := hμreg
  letI := hμright
  exact complementaryEndpoint_of_characterLimit F T hlimit hn A a hAi hAu ha hirr μ

end Langlands.Classification
