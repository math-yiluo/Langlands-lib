import Langlands.Global.AdelicPositiveDecompositionReduction
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Proof of the positive and norm-one adelic decomposition -/

universe u

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme

/-- Every connected reductive group over a number field has an actual split component whose
intrinsic positive adelic points and the norm-one adelic subgroup give the adelic points by
multiplication, as a continuous group equivalence. -/
theorem adelicPositiveDecompositionStatement : AdelicPositiveDecompositionStatement.{u} :=
  adelicPositiveDecomposition_of_centralSplitTorusCharacter centralSplitTorusCharacter

end Langlands.Global.PositiveRealTorus
