import Langlands.GroupScheme.Torus.MultiplicativeTypeStrictHenselianLiftReduction
import Langlands.GroupScheme.Torus.MultiplicativeTypeCompleteLocalDeformationProof

/-! # Prescribed clopen diagonalizable lifts over strictly Henselian local rings -/

universe u

namespace Langlands.GroupScheme

/-- A prescribed special-fibre diagonalization lifts to an actual clopen
homomorphism over any strictly Henselian local ring. -/
theorem multiplicativeTypeStrictHenselianLift :
    MultiplicativeTypeStrictHenselianLiftStatement.{u} :=
  StrictHenselianLiftReduction.multiplicativeTypeStrictHenselianLift_of_completeLocalDeformation
    multiplicativeTypeCompleteLocalDeformation

end Langlands.GroupScheme
