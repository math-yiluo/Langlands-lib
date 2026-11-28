import Langlands.BaseChange.ExternalTensorTwistedCharacter
import Langlands.Representation.CompactCoefficient.CompactFormalDegreeHaarScalingProof

/-! # Product twisted traces for a supplied Haar measure -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis MeasureTheory
open scoped NNReal

private theorem twistedDistribution_smul_measure
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ₀ μ : Measure G) [IsFiniteMeasureOnCompacts μ₀] [μ₀.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant] {r : ℝ≥0} (hr : μ = r • μ₀)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (A : Module.End ℂ V) :
    twistedDistribution μ ρ hρ A = ((r : ℝ) : ℂ) • twistedDistribution μ₀ ρ hρ A := by
  subst μ
  apply LinearMap.ext
  intro f
  rw [← twistedDistribution_smul, twistedDistribution_apply, twistedDistribution_apply]
  apply congrArg FiniteRankEnd.trace
  apply Subtype.ext
  apply LinearMap.ext
  intro w
  change Hecke.integratedAction (r • μ₀) ρ hρ.1 f (A w) =
    Hecke.integratedAction μ₀ ρ hρ.1 f (((r : ℝ) : ℂ) • A w)
  rw [map_smul]
  exact Renard.CompactRepresentation.integratedAction_nnreal_smul_measure μ₀ r ρ hρ.1 f (A w)

universe uI uG uV

variable {ι : Type uI} [Fintype ι] [DecidableEq ι]
  {H : ι → Type uG} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
  [∀ i, IsTopologicalGroup (H i)] [∀ i, SecondCountableTopology (H i)]
  [∀ i, T2Space (H i)] [∀ i, LocallyCompactSpace (H i)]
  [∀ i, TotallyDisconnectedSpace (H i)]
  [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]
  [m : MeasurableSpace (∀ i, H i)] [BorelSpace (∀ i, H i)]

/-- For a supplied Haar measure on a finite product, the product-test trace
identity has one nonzero normalization constant for all factor pairs. -/
def ProductMeasureTwistedTrace (μ : Measure (∀ i, H i)) [μ.IsHaarMeasure]
    (μi : ∀ i, Measure (H i)) [∀ i, (μi i).IsHaarMeasure] : Prop :=
  ∃ a : ℂ, a ≠ 0 ∧
    ∀ {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
      (ρ : ∀ i, Representation ℂ (H i) (V i)) (hρ : ∀ i, IsAdmissible (ρ i))
      (A : ∀ i, Module.End ℂ (V i)) (f : ∀ i, SchwartzBruhat (H i)),
      twistedDistribution μ (FiniteTensor.external ρ)
          (FiniteTensor.isAdmissible_external ρ hρ) (PiTensorProduct.map A)
          (SchwartzBruhat.piTensor f) =
        a * ∏ i, twistedDistribution (μi i) (ρ i) (hρ i) (A i) (f i)

/-- Haar uniqueness transports the product-tensor identity to the supplied
measure, including when its measurable structure is given as `borel`. -/
theorem productMeasureTwistedTrace (μ : Measure (∀ i, H i)) [μ.IsHaarMeasure]
    (μi : ∀ i, Measure (H i)) [∀ i, (μi i).IsHaarMeasure] :
    ProductMeasureTwistedTrace.{uI,uG,uV} μ μi := by
  have hm : m = MeasurableSpace.pi :=
    (@BorelSpace.measurable_eq _ _ m ‹BorelSpace (∀ i, H i)›).trans
      (@BorelSpace.measurable_eq _ _ MeasurableSpace.pi Pi.borelSpace).symm
  subst m
  let r := Measure.haarScalarFactor μ (Measure.pi μi)
  have hr : μ = r • Measure.pi μi := Measure.isMulLeftInvariant_eq_smul μ (Measure.pi μi)
  refine ⟨((r : ℝ) : ℂ), Complex.ofReal_ne_zero.mpr
    (NNReal.coe_ne_zero.mpr (Measure.haarScalarFactor_pos_of_isHaarMeasure μ (Measure.pi μi)).ne'), ?_⟩
  intro V _ _ ρ hρ A f
  rw [twistedDistribution_smul_measure (Measure.pi μi) μ hr, LinearMap.smul_apply, smul_eq_mul,
    twistedDistribution_external_piTensor μi ρ hρ A f]

end Langlands.BaseChange
