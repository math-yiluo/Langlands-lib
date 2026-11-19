import Langlands.Global.AdelicSiegelMeasureReduction
import Langlands.Global.PositiveTorusUnipotentModulus
import Langlands.Global.SimpleRootBoxCompact
import Langlands.Global.UnipotentRationalQuotientCompactProof
import Langlands.GroupScheme.Rational.PositiveTorusTriangularCoordinatesProof
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof

/-! # Finite Haar measure of adelic Siegel sets in the norm-one group -/

universe u

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme

/-- The preimage of the weak Siegel product in the norm-one adelic group has finite left
Haar outer measure for every compact factor datum satisfying the Iwasawa and positive-torus
compatibility hypotheses of the published statement. -/
theorem siegelProductFiniteMeasure : SiegelProductFiniteMeasureStatement.{u} :=
  siegelProductFiniteMeasureStatement_of_inputs
    AdelicGroupPoints.unipotentRationalQuotientCompact
    (positiveTorusUnipotentModulus_of_coordinates positiveTorusTriangularCoordinates)
    (simpleRootBoxCompactStatement_of_rootComplement relativeRootNegation
      relativeCharacterRootComplement)

end Langlands.Global.AdelicSiegelFactors
