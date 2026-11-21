import Langlands.Geometry.Analytic.QuasiEtaleToEtaleReduction
import Langlands.Geometry.Analytic.LocalizedEtalePullbackProof
import Langlands.Geometry.Analytic.EtalePointwiseLifting.LocalizedStability
import Langlands.Geometry.Analytic.EtalePullbackGSpaceProof

/-! # The morphisms of sites from quasi-étale to étale -/

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

/-- The ordinary and equivariant étale inclusions into the quasi-étale sites are
representably flat and continuous. -/
theorem quasiEtaleToEtale : QuasiEtaleToEtaleStatement.{u, v, z} :=
  quasiEtaleToEtale_of_inputs
    (fun K _ _ _ => localizedEtalePullbackBaseChange (K := K))
    (fun K _ _ _ => localizedEtaleStability (K := K))
    (fun K _ _ _ => etalePullbackGSpace K)

end Langlands.Analytic.SaturatedAtlasPresentation
