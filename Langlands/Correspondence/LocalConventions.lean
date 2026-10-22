import Langlands.LocalField.Canonical
import Langlands.HarmonicAnalysis.Basic
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Canonical local conventions for the correspondence

These are concrete specializations of the common harmonic-analysis definitions.
Neither an additive character nor a Fourier self-dual measure is chosen.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

local instance : T2Space F.Carrier := by
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  have := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  infer_instance

local instance : TotallyDisconnectedSpace F.Carrier := by
  let := F.canonicalNormedField
  have : IsUltrametricDist F.Carrier :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := Padic p) (L := F.Carrier))
  change @TotallyDisconnectedSpace F.Carrier
    F.canonicalNormedField.toUniformSpace.toTopologicalSpace
  infer_instance

local instance : MeasurableSpace F.Carrier := borel F.Carrier

local instance : BorelSpace F.Carrier := ⟨rfl⟩

/-- All continuous complex quasi-characters of the actual multiplicative field.
No unitarity condition is imposed. -/
abbrev QuasiCharacter := HarmonicAnalysis.Quasicharacter F.Carrier

/-- The common continuous nontrivial unitary additive-character type,
specialized to the actual p-adic field and its canonical topology. -/
abbrev NontrivialAdditiveCharacter :=
  HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier

/-- The actual compactly supported locally constant complex test functions. -/
abbrev LocalTestFunction := HarmonicAnalysis.SchwartzBruhat F.Carrier

/-- Regular additive Haar measures on the canonical Borel measurable field.
No normalization or existence of a self-dual measure is assumed. -/
abbrev LocalAdditiveHaarMeasure :=
  HarmonicAnalysis.AdditiveHaarMeasure F.Carrier

/-- The plus-sign Fourier transform for the actual field pairing `(x,y) ↦ x*y`.
Its output is a function; preservation of the test space is not assumed. -/
def localFourierTransform (ψ : NontrivialAdditiveCharacter F)
    (μ : LocalAdditiveHaarMeasure F) :
    LocalTestFunction F →ₗ[ℂ] (F.Carrier → ℂ) :=
  HarmonicAnalysis.fourierTransform ψ μ

/-- Intrinsic self-duality: the second Fourier integral converges on every
test function and the iterated transform is `f(-x)`. This is a proposition,
not an assumed theorem or a chosen measure. -/
def IsSelfDualMeasure (ψ : NontrivialAdditiveCharacter F)
    (μ : LocalAdditiveHaarMeasure F) : Prop :=
  HarmonicAnalysis.IsSelfDual ψ μ

end Langlands.Correspondence
