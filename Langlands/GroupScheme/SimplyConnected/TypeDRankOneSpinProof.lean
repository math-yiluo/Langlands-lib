import Langlands.GroupScheme.SimplyConnected.TypeDRankOneSpinIndexReduction
import Langlands.GroupScheme.SimplyConnected.ClassicalTypeDSpinPresentationProof

/-!
# Quaternionic spin covers from rank-one type-D indices

The general classical type-D spin presentation supplies the premise of the
published rank-one index reduction.
-/

universe u

namespace Langlands.GroupScheme

/-- A rank-one outer `D₄` or inner `D₅` index gives an actual quaternionic
spin cover over every field, including characteristic two. -/
theorem typeDRankOneSpin : TypeDRankOneSpinStatement.{u} :=
  typeDRankOneSpin_of_classicalTypeDSpinPresentation classicalTypeDSpinPresentation

end Langlands.GroupScheme
