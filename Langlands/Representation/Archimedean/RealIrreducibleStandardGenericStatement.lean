import Langlands.Representation.Archimedean.GKModule
import Langlands.Representation.Archimedean.RealStandardModuleGKModule

/-! # Irreducible real standard modules are generic -/

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

/-- If the `O(n)`-finite standard module of a list of real blocks of rank `n` is irreducible,
then it is generic: some nonzero linear functional transforms under the strictly upper
triangular real matrices by the differential of a nondegenerate unitary character of the upper
unipotent group. -/
def RealIrreducibleStandardGenericStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
    IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds) →
    IsRealGenericGKModule n (realStandardLie n ds)

end Langlands.Archimedean
