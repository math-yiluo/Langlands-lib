import Langlands.Representation.Classification.OrderedMultisegmentHeadReduction
import Langlands.Representation.Classification.OrderedSegmentSquareIntegrableConversionProof
import Langlands.Representation.Classification.SquareIntegrableEqualExponentGroupingProof
import Langlands.Representation.Classification.RegularLanglandsHeadExistenceProof

/-! Strong irreducible heads of ordered products of special segment heads. -/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every nonprecedence-ordered product of supplied special segment heads has
an actual smooth irreducible head, with equality of all irreducible quotient
kernels, including the empty product in rank zero. -/
theorem orderedMultisegmentHeadExistence :
    OrderedMultisegmentHeadExistence.{uF, uV} F T :=
  orderedMultisegmentHeadExistence_of_prerequisites.{uF, uV} F T
    (orderedSegmentSquareIntegrableConversion.{uF, uV} F T)
    (squareIntegrableEqualExponentGrouping.{uF, uV} F T)
    glRegularLanglandsHeadExistence.{uF, uV}

end Langlands.Classification
