import Langlands.CommutativeAlgebra.StrictHenselianDvrExtension
import Langlands.GroupScheme.Reductive.NoetherianIsogenyApproximation
import Langlands.GroupScheme.Reductive.QuasiFiniteNoetherianModelProof
import Langlands.GroupScheme.Reductive.SpecialFibreIsogenyRigidity
import Langlands.GroupScheme.Reductive.StrictHenselianDvrKernelRemovalProof

/-! # Fibrewise isogenies of reductive group schemes are isogenies -/

universe u

namespace Langlands.GroupScheme

/-- A homomorphism of reductive group schemes which is an isogeny on every
residue-field fibre is an isogeny over the original arbitrary base scheme. -/
theorem reductiveFibrewiseIsogeny : ReductiveFibrewiseIsogenyStatement.{u} :=
  reductiveFibrewiseIsogeny_of_noetherianModel_and_dvr
    reductiveQuasiFiniteNoetherianModel
    (dvrFibrewiseIsogeny_of_strictHenselian_and_extension
      Langlands.CommutativeAlgebra.strictHenselianDvrExtension
      (strictHenselianDvrFibrewiseIsogeny_of_kernelRemoval_and_rigidity
        strictHenselianDvrKernelRemoval strictHenselianDVRIsogenyRigidity))

end Langlands.GroupScheme
