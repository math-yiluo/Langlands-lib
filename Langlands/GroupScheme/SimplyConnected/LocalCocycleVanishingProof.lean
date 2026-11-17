import Langlands.GroupScheme.SimplyConnected.LocalCocycleVanishingChamberReduction
import Langlands.GroupScheme.SimplyConnected.LocalUnramifiedChamberProof

/-! # Local vanishing of simply connected cocycles on finite separable covers -/

universe u

namespace Langlands.GroupScheme

/-- **Local vanishing for simply connected groups.** Every cocycle of a simply connected group
over a nonarchimedean local field, on a finite separable field cover, is trivial. The published
reduction `localSimplyConnectedCocycleVanishingChamberReduction` is applied to the published
Galois-stable Iwahori chamber theorem `localSimplyConnectedUnramifiedChamber`. -/
theorem localSimplyConnectedCocycleVanishing :
    LocalSimplyConnectedCocycleVanishingStatement.{u} :=
  localSimplyConnectedCocycleVanishingChamberReduction localSimplyConnectedUnramifiedChamber

end Langlands.GroupScheme
