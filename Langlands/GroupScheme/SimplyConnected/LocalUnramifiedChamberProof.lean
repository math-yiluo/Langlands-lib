import Langlands.GroupScheme.SimplyConnected.LocalUnramifiedChamberAssembly
import Langlands.GroupScheme.SimplyConnected.LocalUnramifiedIwahoriModelProof
import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitProof
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction
import Langlands.Geometry.Building.SpecialTorusExistenceProof
import Langlands.Geometry.Building.MaximalUnramifiedAffineWeylProof
import Langlands.Geometry.Building.UnramifiedBuildingMetricProof
import Langlands.Geometry.Building.UnramifiedTwistedChamberReduction
import Langlands.Geometry.Building.UnramifiedTwistedChamberThroughFixedPointReduction
import Langlands.Geometry.Building.UnramifiedTwistedChamberQuotientReduction
import Langlands.Geometry.Building.UnramifiedTwistedChamberQuotientProof

/-! # Proof of the Galois-stable Iwahori chamber input over the maximal unramified extension -/

universe u

namespace Langlands.GroupScheme

open Langlands.Geometry.Building

/-- **Galois-stable Iwahori chamber over the maximal unramified extension.** The published
conditional assembly `localSimplyConnectedUnramifiedChamberAssembly` is applied to published
proofs of its five inputs: quasi-splitness over the maximal unramified extension (from
`henselianDiscreteQuasiSplit`), existence of a special torus, the affine Weyl group input
over the maximal unramified extension, the twisted-stable chamber statement (assembled from
the published metric, through-fixed-point, generator and quotient results), and the
simply connected Iwahori model statement. -/
theorem localSimplyConnectedUnramifiedChamber :
    LocalSimplyConnectedUnramifiedChamberStatement.{u} :=
  localSimplyConnectedUnramifiedChamberAssembly
    (unramifiedQuasiSplit_of_henselianDiscrete henselianDiscreteQuasiSplit)
    specialTorusExistence maximalUnramifiedAffineWeyl
    (unramifiedTwistedChamber_of_metric unramifiedBuildingMetric
      (unramifiedTwistedChamberThroughFixedPointReduction
        (unramifiedTwistedGeneratorChamber_of_quotient unramifiedTwistedChamberQuotient)))
    localSimplyConnectedUnramifiedIwahoriModel

end Langlands.GroupScheme
