import Langlands.Representation.RankinSelberg.InducedTailSpanStatement
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeStatement
import Langlands.Representation.RankinSelberg.SymmetricLPolynomialExistenceStatement
import Langlands.Representation.RankinSelberg.TwoBlockMultiplicativityStatement
import Langlands.Representation.Parabolic.ThreeBlockInductionAssociativityStatement
import Langlands.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedStatement

/-!
# Conditional assembly interface for induced tail divisibility

An internal implication collecting the six separately owned prerequisites for
the tail L-polynomial proof. This proposition does not supply those inputs or
assert the closed parent theorem.
-/

namespace Langlands.RankinSelberg

universe uF uV₁ uV₂ uW

/-- The direct-span and ramified-enlargement inputs imply the unchanged
four-universe tail statement. All premises use a common carrier universe
containing the field and the three original carriers. -/
def InducedTailConditionalAssemblyStatement : Prop :=
  InducedTailSpanStatement.{uF, max uF uV₁ uV₂ uW,
    max uF uV₁ uV₂ uW, max uF uV₁ uV₂ uW} →
  NormalizedProductWhittakerTypeStatement.{uF, max uF uV₁ uV₂ uW} →
  SymmetricLPolynomialExistenceStatement.{uF, max uF uV₁ uV₂ uW,
    max uF uV₁ uV₂ uW} →
  TwoBlockLFactorMultiplicativityStatement.{uF, max uF uV₁ uV₂ uW,
    max uF uV₁ uV₂ uW} →
  Parabolic.ThreeBlockInductionAssociativityStatement.{uF, max uF uV₁ uV₂ uW,
    max uF uV₁ uV₂ uW, max uF uV₁ uV₂ uW} →
  WhittakerTypeHighlyRamifiedLVanishingStatement.{uF, 0, max uF uV₁ uV₂ uW} →
  InducedTailLFactorStatement.{uF, uV₁, uV₂, uW}

end Langlands.RankinSelberg
