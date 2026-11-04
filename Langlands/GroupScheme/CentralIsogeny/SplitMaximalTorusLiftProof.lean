import Langlands.GroupScheme.CentralIsogeny.SplitTorusLiftComposition
import Langlands.GroupScheme.CentralIsogeny.KernelTorsion

/-! # Split maximal tori lift through central isogenies -/

universe u

namespace Langlands.GroupScheme

/-- A split maximal torus of the target of a central isogeny of connected
reductive groups lifts to a split maximal torus of the source. -/
theorem centralIsogenySplitMaximalTorusLift :
    CentralIsogenySplitMaximalTorusLiftStatement.{u} :=
  splitMaximalTorusLift_of_kernel_exponent
    fun _ _ _ _ _ _ _ hπ => hπ.exists_pow_eq_one_kernel

end Langlands.GroupScheme
