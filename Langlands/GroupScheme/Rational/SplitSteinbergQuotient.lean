import Langlands.GroupScheme.Rational.SteinbergGeometricReduction
import Langlands.GroupScheme.Rational.SteinbergTriangularCoordinates
import Langlands.GroupScheme.Rational.FundamentalCharacterGenerationProof
import Langlands.GroupScheme.Rational.FundamentalRepresentationsAssembly
import Langlands.GroupScheme.Rational.DominantHighestWeightProof
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof

/-! # Steinberg's cross-section isomorphism for the canonical class quotient -/

universe u

namespace Langlands.GroupScheme

/-- **Steinberg's cross-section isomorphism** (Steinberg 1965, Theorem 7.9). For a simply
connected group with supplied split pinning over an arbitrary field, the supplied ordered
product `SplitPinning.steinbergProduct e x n` followed by the canonical class quotient map
`ClassFunctions.rho G` is an isomorphism, for every ordering, normalized simple-root family
and simple-reflection family. -/
theorem splitSteinbergQuotient : SplitSteinbergQuotientStatement.{u} :=
  splitSteinbergQuotient_of_algClosed
    (fun k _ G hG => isSimplyConnectedFieldExtension k (AlgebraicClosure k) G hG)
    (fun k _ _ G _ p hG r e x n =>
      splitSteinbergQuotient_algClosed_of_character_inputs
        (splitFundamentalRepresentationsExist_of_corootSpan_of_highestWeight
          splitSimplyConnectedCorootSpan splitDominantHighestWeightRepresentationsExist)
        splitFundamentalCharacterGeneration splitSteinbergCharacterTriangular
        k G p hG r e x n)

end Langlands.GroupScheme
