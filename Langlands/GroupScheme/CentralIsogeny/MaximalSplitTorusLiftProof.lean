import Langlands.GroupScheme.CentralIsogeny.MaximalSplitTorusLift
import Langlands.GroupScheme.CentralIsogeny.KernelTorsion

/-! # Maximal split tori lift under central isogenies -/

universe u

namespace Langlands.GroupScheme

/-- Every maximal split torus of the target of a central isogeny of connected reductive groups
over a field lifts to a maximal split torus of the source, through a flat surjective homomorphism
of finite presentation. -/
theorem centralIsogenyMaximalSplitTorusLift :
    CentralIsogenyMaximalSplitTorusLiftStatement.{u} :=
  CentralSplitTorusLift.statement_of_kernel_exponent
    fun _ _ _ _ _ _ _ hπ => hπ.exists_pow_eq_one_kernel

end Langlands.GroupScheme
