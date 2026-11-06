import Langlands.GroupScheme.Reductive.SplitRootLieLineStatement
import Langlands.GroupScheme.Reductive.RootLieLineFromTangent
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Proof: root Lie spaces of split maximal tori are lines -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over an arbitrary field, each root space of an actual split maximal torus
in a connected reductive group is a free module of rank one. -/
theorem splitRootLieLine : SplitRootLieLineStatement.{u} :=
  fun k _ G hG T hT i hi =>
    rootLieLine_of_twoStructuralInputs dynamicCentralizerReductive maximalTorusBaseChange
      k G hG T hT i hi

end Langlands.GroupScheme
