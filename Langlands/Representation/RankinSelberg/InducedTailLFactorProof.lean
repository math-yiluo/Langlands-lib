import Langlands.Representation.RankinSelberg.InducedTailConditionalAssemblyProof
import Langlands.Representation.RankinSelberg.InducedTailSpanProof
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.Representation.RankinSelberg.SymmetricLPolynomialExistenceProof
import Langlands.Representation.RankinSelberg.TwoBlockLFactorMultiplicativityProof
import Langlands.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedProof
import Langlands.Representation.Parabolic.ThreeBlockInductionAssociativityProof

/-!
# Tail L-polynomial divisibility for upper two-block induction

The closed four-universe theorem follows from the published conditional
assembly by supplying all six prerequisites with closed Library theorems.
-/

namespace Langlands.RankinSelberg

universe uF uV₁ uV₂ uW

/-- The certified L-polynomial of the ordered second block divides that of
the actual normalized upper two-block induction against any positive-rank
Whittaker-type test representation. Both certified polynomials exist. -/
theorem inducedTailLFactor :
    InducedTailLFactorStatement.{uF, uV₁, uV₂, uW} :=
  inducedTailConditionalAssembly.{uF, uV₁, uV₂, uW}
    (inducedTailSpan.{uF, max uF uV₁ uV₂ uW,
      max uF uV₁ uV₂ uW, max uF uV₁ uV₂ uW})
    (normalizedProductWhittakerType.{uF, max uF uV₁ uV₂ uW})
    (symmetricLPolynomialExists.{uF, max uF uV₁ uV₂ uW,
      max uF uV₁ uV₂ uW})
    (twoBlockLFactorMultiplicativity.{uF, max uF uV₁ uV₂ uW,
      max uF uV₁ uV₂ uW})
    (Parabolic.threeBlockInductionAssociativity.{uF, max uF uV₁ uV₂ uW,
      max uF uV₁ uV₂ uW, max uF uV₁ uV₂ uW})
    (whittakerTypeHighlyRamifiedLVanishing.{uF, 0, max uF uV₁ uV₂ uW})

end Langlands.RankinSelberg
