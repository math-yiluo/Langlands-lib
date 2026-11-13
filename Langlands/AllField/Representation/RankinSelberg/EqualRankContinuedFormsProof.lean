import Langlands.Representation.RankinSelberg.EqualRankContinuedFormsProof
import Langlands.AllField.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement
/-!
# Construction of the continued normalized equal-rank trilinear forms

The cleared rational continuations of the original and Fourier-dual equal-rank
integrals have unique Laurent lifts, linear in the test triple. Evaluating them at
the nonzero spectral points `q^(-s)` and `q^(-(1-s))` gives trilinear forms for
every complex parameter. Their twisted invariance follows from the monomial
translation laws of the lifts, and they agree with the normalized rational
continuations wherever the relevant continuation is regular.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankFunctionalEquationStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow padic_row_instances
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

section RowFourierMap

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {d : ℕ} [BorelSpace (Fin d → F)]
  {ψ : UnitaryAdditiveCharacter F} {ν : AdditiveHaarMeasure F} [SigmaFinite ν.measure]

end RowFourierMap

section Determinant

variable {F : Type uF} [Field F] {d : ℕ}

end Determinant

section Spectral

end Spectral

section Padic

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- The normalized absolute value of the determinant of an invertible matrix is
an integer power of the residue cardinality. -/
theorem normalizedAbsoluteValue_det_eq_zpow {d : ℕ}
    (g : Langlands.GeneralLinear d F) :
    normalizedAbsoluteValue T (Matrix.det g.val) =
      (T.residueCardinality : ℝ) ^ (-T.ord (Matrix.det g.val)) := by
  rw [normalizedAbsoluteValue_apply,
    T.normalizedAbs_of_ne_zero (Matrix.isUnits_det_units g).ne_zero]

/-- Borel structure on rows and sigma-finiteness of the scalar Haar measure in
the instance context of the continued-forms statement. -/
theorem padic_row_instances (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := IsTopologicalAddGroup.rightUniformSpace F
    letI := isUniformAddGroup_of_addCommGroup (G := F)
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ ν : AdditiveHaarMeasure F,
      BorelSpace (Fin (n + 1) → F) ∧ SigmaFinite ν.measure := by
  intro ν
  let := T.topology
  let := borel F
  have : BorelSpace F := ⟨rfl⟩
  have : SecondCountableTopology F := T.secondCountableTopology
  have : SigmaCompactSpace F := T.sigmaCompactSpace
  exact ⟨inferInstance, inferInstance⟩

end Padic

section LaurentSpectral

end LaurentSpectral

section Assembly

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ψ : UnitaryAdditiveCharacter F} {μ : Measure (LeftUnipotentQuotient n F)}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}
  {q : ℕ} {abv : AbsoluteValue F ℝ}

variable [MeasurableSpace F]

end Assembly

end Langlands.AllField.RankinSelberg
