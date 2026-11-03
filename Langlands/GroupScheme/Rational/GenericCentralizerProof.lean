import Langlands.GroupScheme.Rational.GenericCentralizerReduction
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Lie.SubgroupEqualityProof

/-! # The centralizer of a maximal split torus is the dynamic centralizer of a generic
cocharacter -/

universe u

namespace Langlands.GroupScheme

/-- For a connected reductive group over a field, a maximal split torus `T` and a generic
cocharacter `ν` of `T`, the dynamic centralizer of `ν` is the centralizer of `T`. -/
theorem genericCentralizer : GenericCentralizerStatement.{u} :=
  genericCentralizerStatement_of dynamicSmooth dynamicConnected dynamicLie lieSubgroupEquality

end Langlands.GroupScheme
