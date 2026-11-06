import Langlands.GroupScheme.Rational.LeviSplitComponentReduction
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Split components of dynamic Levi subgroups -/

universe u

namespace Langlands.GroupScheme

/-- Over every field, a closed representative `M` of the dynamic centralizer of `μ ≫ i`, for a
maximal split torus `i : T ⟶ G` of a connected reductive `G`, is connected reductive, and every
split component of `G` factors through a split component of `M` that factors through `i`, with the
induced character restrictions composing to the restriction from `G`. -/
theorem leviSplitComponentStatement : LeviSplitComponentStatement.{u} :=
  leviSplitComponentStatement_of_dynamicCentralizerReductive dynamicCentralizerReductive

example : LeviSplitComponentStatement.{u} := @leviSplitComponentStatement.{u}

end Langlands.GroupScheme
