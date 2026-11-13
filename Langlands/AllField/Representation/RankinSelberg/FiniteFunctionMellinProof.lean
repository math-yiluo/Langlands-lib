import Langlands.Representation.RankinSelberg.FiniteFunctionMellinProof
import Langlands.AllField.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.AllField.Representation.RankinSelberg.FiniteFunctionMellinStatement
import Langlands.AllField.Representation.RankinSelberg.OneVariableMellinProof
noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding FiniteFunctionMellinStatement FiniteFunctionShellSeriesStatement OneVariableMellinStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankFunctionalEquationStatement ValuationShellIntegrationStatement continuous_ord_units finiteFunctionMellin finiteFunctionShellSeries normalizedAbsoluteValue normalizedAbsoluteValue_apply oneVariableMellin valuationShellIntegration
open Langlands.AllField.RankinSelberg

open MeasureTheory Polynomial
open scoped BigOperators

namespace MellinAssembly
open Langlands.RankinSelberg.MellinAssembly hiding field_totallyDisconnected finiteFunctionMellin_of_inputs localHaar_sigmaFinite
open Langlands.AllField.RankinSelberg.MellinAssembly
open Langlands.RankinSelberg hiding FiniteFunctionMellinStatement FiniteFunctionShellSeriesStatement OneVariableMellinStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankFunctionalEquationStatement ValuationShellIntegrationStatement continuous_ord_units finiteFunctionMellin finiteFunctionShellSeries normalizedAbsoluteValue normalizedAbsoluteValue_apply oneVariableMellin valuationShellIntegration
open Langlands.AllField.RankinSelberg

universe u

theorem localHaar_sigmaFinite 
    (F : Type*) [Field F] (T : LocalFieldData F) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel Fˣ
    letI : BorelSpace Fˣ := ⟨rfl⟩
    SigmaFinite (localMultiplicativeHaar F) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel Fˣ
  let : BorelSpace Fˣ := ⟨rfl⟩
  let := T.fieldT2
  let := T.secondCountableTopology
  let : SecondCountableTopology Fˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  unfold localMultiplicativeHaar multiplicativeHaar normalizedCompactOpenHaar
  infer_instance

theorem field_totallyDisconnected 
    (F : Type*) [Field F] (T : LocalFieldData F) :
    letI := T.topology
    TotallyDisconnectedSpace F := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation F)
  infer_instance

open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement SchwartzBruhatValuationBoundsStatement padicScalarHaarScaling schwartzBruhatValuationBounds in
open Langlands.AllField.HarmonicAnalysis in
theorem finiteFunctionMellin_of_inputs
    (htensor : FiniteFunctionTensorStatement.{u})
    (hscalar : OneVariableMellinStatement.{u}) :
    FiniteFunctionMellinStatement.{u} := by
  intro F _ T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel Fˣ
  let : BorelSpace Fˣ := ⟨rfl⟩
  let := T.fieldT2
  let := field_totallyDisconnected F T
  let := localHaar_sigmaFinite F T
  dsimp only
  intro r m hm X hX
  apply mellin_family_of_each (Measure.pi (fun _ : Fin r => localMultiplicativeHaar F))
    T.residueCardinality X
  intro η hη
  obtain ⟨n, c, f, hf, he⟩ := htensor Fˣ r η (hX η hη)
  have hs (j : Fin n) (i : Fin r) :=
    hscalar F T (m i) (hm i) (f j i) (hf j i).1 (hf j i).2
  apply mellin_of_expansions (localMultiplicativeHaar F)
    T.residueCardinality T.residueCardinality_gt_one r n η c f he
    (fun Φ : SchwartzBruhat (Fin r → F) => fun a => Φ (fun i => (a i : F)))
    (fun φ : SchwartzBruhat F => fun a => φ (a : F))
    ?_ (fun i s a => (T.normalizedAbs (a : F) : ℂ) ^ ((m i : ℂ) * s))
    (fun j i => (hs j i).1) (fun j i => (hs j i).2.1) (fun j i => (hs j i).2.2)
  intro Φ
  obtain ⟨N, d, φ, hφ⟩ := rowTensorDecomposition F r Φ
  exact ⟨N, d, φ, fun a => hφ (fun i => (a i : F))⟩

end MellinAssembly

universe uF

/-- Actual torus Mellin convergence, rational continuation, and a Laurent
denominator uniform over the finite family and all Schwartz--Bruhat tests. -/
theorem finiteFunctionMellin : FiniteFunctionMellinStatement.{uF} :=
  Langlands.AllField.RankinSelberg.MellinAssembly.finiteFunctionMellin_of_inputs
    finiteFunctionTensor.{uF} oneVariableMellin.{uF}

end Langlands.AllField.RankinSelberg
