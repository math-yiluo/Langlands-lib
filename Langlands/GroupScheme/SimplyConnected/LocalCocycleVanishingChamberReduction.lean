import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitProof
import Langlands.GroupScheme.SimplyConnected.LocalCocycleVanishingGaloisReduction
import Langlands.GroupScheme.SimplyConnected.LocalGaloisCocycleVanishingUnramifiedReduction
import Langlands.GroupScheme.SimplyConnected.LocalUnramifiedSplittingReduction
import Langlands.GroupScheme.SimplyConnected.LocalUnramifiedIntegralTwistReduction
import Langlands.GroupScheme.SimplyConnected.LocalUnramifiedChamberReduction
import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitReduction
import Langlands.GroupScheme.Rational.QuasiSplitRegularClassRational
import Langlands.GroupScheme.Rational.QuasiSplitCocycleTorusReductionProof

/-! # Local vanishing of simply connected cocycles from the Galois-stable chamber -/

universe u

namespace Langlands.GroupScheme

/-- Every cocycle of a simply connected group over a nonarchimedean local field on a finite
Galois cover becomes trivial over a finite unramified extension. -/
theorem localSimplyConnectedUnramifiedSplitting :
    LocalSimplyConnectedUnramifiedSplittingStatement.{u} :=
  localSimplyConnectedUnramifiedSplitting_of_steinberg henselianDiscreteQuasiSplit
    quasiSplitCocycleTorusReduction

/-- The Galois-stable chamber with its Iwahori model over the maximal unramified extension
implies vanishing of cocycles of simply connected groups over nonarchimedean local fields on
finite separable covers. -/
def LocalSimplyConnectedCocycleVanishingChamberReductionStatement : Prop :=
  LocalSimplyConnectedUnramifiedChamberStatement.{u} →
    LocalSimplyConnectedCocycleVanishingStatement.{u}

/-- Proof of the reduction: compose the published reductions. -/
theorem localSimplyConnectedCocycleVanishingChamberReduction :
    LocalSimplyConnectedCocycleVanishingChamberReductionStatement.{u} := fun hC =>
  localSimplyConnectedCocycleVanishing_of_galois
    (localSimplyConnectedGaloisCocycleVanishing_of_unramified
      localSimplyConnectedUnramifiedSplitting
      (localSimplyConnectedUnramifiedIntegralTwistReduction
        (localSimplyConnectedUnramifiedChamberReduction hC)))

end Langlands.GroupScheme
