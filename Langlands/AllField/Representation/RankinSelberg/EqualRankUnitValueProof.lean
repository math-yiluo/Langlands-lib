import Langlands.Representation.RankinSelberg.EqualRankUnitValueProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankCompactTest
import Langlands.AllField.Representation.RankinSelberg.EqualRankUnitValueStatement
import Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement
import Langlands.AllField.Representation.Whittaker.WhittakerTypeKirillovProof
/-!
# An actual equal-rank JPSS integral with rational value one

Apply the proved Kirillov inclusion in both representation universes to the
compact coefficient-test construction, then normalize its actual integral.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankUnitValueStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement equalRankUnitValue hasEqualRankCompactTest_of_kirillov lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement exists_compactOpen_glCoefficientRightStabilizer mirabolicUnitTest modelKirillovTransfer
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

/-- Actual coefficient vectors and a Schwartz--Bruhat function give rational
value one for every compatible equal-rank quotient measure. -/
theorem equalRankUnitValue
    (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) :
    EqualRankUnitValueStatement.{uF, uV, uW} F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro ψ _ μ hμ V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ'
  exact (hasEqualRankCompactTest_of_kirillov
    Langlands.AllField.whittakerTypeKirillov.{uF, uV}
    Langlands.AllField.whittakerTypeKirillov.{uF, uW}
    F T n ψ V W π σ hπ hσ ℓ ℓ' hℓ hℓ').one_mem_equalRankRationalValues
      hμ T.residueCardinality

end Langlands.AllField.RankinSelberg
