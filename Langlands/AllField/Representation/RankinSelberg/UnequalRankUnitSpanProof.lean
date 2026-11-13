import Langlands.Representation.RankinSelberg.UnequalRankUnitSpanProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicUnitTestProof
import Langlands.AllField.Representation.Whittaker.ModelKirillovProof
import Langlands.AllField.Representation.Whittaker.WhittakerTypeKirillovProof
/-! # Unit membership in every actual unequal-rank JPSS zeta span -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.UnitSpanAssembly
open Langlands.RankinSelberg.UnitSpanAssembly hiding unitSpan_of_compact_test unitSpan_of_kirillov_and_compact_test
open Langlands.AllField.RankinSelberg.UnitSpanAssembly
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankMirabolicUnitTestStatement UnequalRankUnitSpanStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply unequalRankMirabolicUnitTest unequalRankUnitSpan
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicCompactMinimalityStatement ModelKirillovTransferStatement mirabolicCompactMinimality modelKirillovTransfer
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear

universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

end Langlands.AllField.RankinSelberg.UnitSpanAssembly

namespace Langlands.AllField.RankinSelberg.UnitSpanAssembly
open Langlands.RankinSelberg.UnitSpanAssembly hiding unitSpan_of_compact_test unitSpan_of_kirillov_and_compact_test
open Langlands.AllField.RankinSelberg.UnitSpanAssembly
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankMirabolicUnitTestStatement UnequalRankUnitSpanStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply unequalRankMirabolicUnitTest unequalRankUnitSpan
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicCompactMinimalityStatement ModelKirillovTransferStatement mirabolicCompactMinimality modelKirillovTransfer
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

/-- Assemble the compact test and its actual coefficient lift using the exact interfaces. -/
theorem unitSpan_of_kirillov_and_compact_test 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n j k : ℕ)
    (hKirillov : Langlands.AllField.WhittakerTypeKirillovStatement.{uF, uV})
    (hTest : UnequalRankMirabolicUnitTestStatement.{uF, uW} F T n j k) :
    UnequalRankUnitSpanStatement.{uF, uV, uW} F T n j k := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro ψ hright μ hμ ν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ'
  obtain ⟨φ, f', hφ, hunit⟩ := hTest ψ μ hμ ν W σ hσ ℓ' hℓ'
  obtain ⟨f, hlift⟩ := Langlands.AllField.Whittaker.modelKirillovTransfer.{uF, uV}
    hKirillov F T (n + (j + k + 1)) V π ψ hπ ℓ hℓ φ hφ
  exact one_mem_of_mirabolic_unit_integral T.residueCardinality ψ
    (normalizedAbsoluteValue T) j k μ (rectangularMeasure ν j (n + 1))
    π σ ℓ ℓ' f f' φ hlift (fun s => (hunit s).2)

/-- Use Whittaker-type Kirillov surjectivity (`whittakerTypeKirillov`) to lift a
supplied compact test into the specified model. -/
theorem unitSpan_of_compact_test 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n j k : ℕ)
    (hTest : UnequalRankMirabolicUnitTestStatement.{uF, uW} F T n j k) :
    UnequalRankUnitSpanStatement.{uF, uV, uW} F T n j k :=
  unitSpan_of_kirillov_and_compact_test F T n j k
    Langlands.AllField.whittakerTypeKirillov.{uF, uV} hTest

end Langlands.AllField.RankinSelberg.UnitSpanAssembly

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankMirabolicUnitTestStatement UnequalRankUnitSpanStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply unequalRankMirabolicUnitTest unequalRankUnitSpan
open Langlands.AllField.RankinSelberg

/-- Every actual unequal-rank JPSS zeta span contains one. -/
theorem unequalRankUnitSpan.{uF, uV, uW} 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n j k : ℕ) :
    UnequalRankUnitSpanStatement.{uF, uV, uW} F T n j k :=
  Langlands.AllField.RankinSelberg.UnitSpanAssembly.unitSpan_of_compact_test F T n j k
    (unequalRankMirabolicUnitTest.{uF, uW} F T n j k)

end Langlands.AllField.RankinSelberg
