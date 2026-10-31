import Langlands.Representation.RankinSelberg.TwoBlockWhittakerDeformationStatement
import Langlands.Representation.RankinSelberg.TwoBlockDeformationAssembly
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof

/-!
# Proof of the entire Whittaker deformation for two lower-induced blocks

Proof of `Langlands.RankinSelberg.TwoBlockWhittakerDeformationStatement`: the conditional
assembly `TwoBlockDeformation.twoBlockWhittakerDeformationStatement_of_normalizedProduct`
applied to the closed theorem `normalizedProductWhittakerType`.
-/

namespace Langlands.RankinSelberg

universe uF uW

/-- JPSS 1983, Lemma of Section (4.5), printed pages 408-409, in its inverse-character
form: every inverse-character Whittaker coefficient of `ρ₀` is the value at `0` of an entire
family of such coefficients of `ρ_u` with one compact open right stabilizer. -/
theorem twoBlockWhittakerDeformation : TwoBlockWhittakerDeformationStatement.{uF, uW} :=
  TwoBlockDeformation.twoBlockWhittakerDeformationStatement_of_normalizedProduct
    normalizedProductWhittakerType.{uF, uW}

end Langlands.RankinSelberg
