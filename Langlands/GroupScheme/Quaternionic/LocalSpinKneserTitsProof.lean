import Langlands.GroupScheme.Quaternionic.SpinLeviLift
import Langlands.GroupScheme.Quaternionic.DegreeTwoNormOneSimplyConnectedProof
import Langlands.GroupScheme.Quaternionic.SpinKernelGeneratorProof
import Langlands.GroupScheme.Quaternionic.KneserThreeSpinSubgroupProof

/-!
# The Kneser–Tits property of quaternionic spin groups of Witt index one

Over a nonarchimedean local field `K`, let `D` be a quaternion central division algebra with an
involution `σ` of the first kind whose symmetric subspace has dimension `3`. Every spin group `S`
of a nondegenerate `σ`-quadratic form on `D^m` (`m = 4` or `5`) of Witt index `1` satisfies
`parabolicElementarySubgroup S = ⊤`. The proof assembles the three spin-kernel statements of
`SpinKernelAssembly`.
-/

universe u

namespace Langlands.GroupScheme.Quaternionic

/-- **Kneser–Tits for quaternionic spin groups of Witt index one over nonarchimedean local
fields.** -/
theorem localSpinKneserTits : LocalSpinKneserTitsStatement.{u} :=
  SpinKernel.localSpinKneserTits_of_spinKernel
    (SpinKernel.spinLeviLift_of_degreeTwoNormOneSimplyConnected
      CentralSimpleUnits.degreeTwoNormOneSimplyConnected)
    SpinKernel.spinKernelGenerator
    SpinKernel.spinKernelElementaryLift

end Langlands.GroupScheme.Quaternionic
