import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerTorusSumProof
import Langlands.AllField.HarmonicAnalysis.ConductorSupplement
import Langlands.AllField.LocalField.SmoothCharacterNormProofSupplement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement
import Langlands.AllField.Representation.RankinSelberg.DiagonalUnipotentHaar
import Langlands.AllField.Representation.RankinSelberg.SquareIntegrableWhittakerTorusSumCoefficient
import Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicUnitTestProof
import Langlands.AllField.Representation.Whittaker.MirabolicUnitTestProof
import Langlands.AllField.Representation.Whittaker.SmoothSimpleRootSupportProof
/-!
# Square-summability of square-integrable Whittaker functions on the torus lattice

The proof compares Whittaker functions with matrix coefficients. By the simple-root support
bound, a Whittaker function vanishes at `ϖ^μ` unless `μ` lies in a translate of the antitone
cone. On the antitone cone, a Whittaker function agrees with a smooth `K(r)`-invariant
matrix coefficient, and square-integrability modulo the centre makes these values
square-summable against the inverse modulus.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement diagonalConj_map normalizedAbsoluteValue normalizedAbsoluteValue_apply singleton_modulus_real
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV

namespace SquareIntegrableWhittakerTorusSum
open Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum hiding exists_smooth_eq_on_antitone normalizedAbs_zpow
open Langlands.AllField.RankinSelberg.SquareIntegrableWhittakerTorusSum
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement diagonalConj_map normalizedAbsoluteValue normalizedAbsoluteValue_apply singleton_modulus_real
open Langlands.AllField.RankinSelberg

variable {F : Type uF} [Field F] (T : LocalFieldData F) {m : ℕ}

theorem normalizedAbs_zpow (a : Fˣ) (d : ℤ) :
    T.normalizedAbs ((a ^ d : Fˣ) : F) = T.normalizedAbs (a : F) ^ d := by
  rw [← T.normalizedAbsUnits_coe, ← T.normalizedAbsUnits_coe, map_zpow,
    Units.val_zpow_eq_zpow_val, NNReal.coe_zpow]

end SquareIntegrableWhittakerTorusSum

open Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum hiding exists_smooth_eq_on_antitone normalizedAbs_zpow
open Langlands.AllField.RankinSelberg.SquareIntegrableWhittakerTorusSum

end Langlands.AllField.RankinSelberg
