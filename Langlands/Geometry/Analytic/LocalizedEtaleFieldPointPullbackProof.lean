import Langlands.Geometry.Analytic.EtaleFieldPointPullbackAssembly
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCompletedResidueProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteBanachPushout.Proof

/-! # Full field-point preservation of localized etale pullbacks -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [IsAlgClosed L] [NormedAlgebra K L]

/-- The actual localized full field-point functor preserves every genuine
pullback square with an etale first cospan leg, in independent universes. -/
theorem localizedEtaleFieldPointPullback :
    LocalizedEtaleFieldPointPullbackStatement.{u, v, uL} K L :=
  localizedEtaleFieldPointPullbackStatement_of_algebra
    PresentedAffinoidAlgebra.domainCompletedResidueSurjectivity
    (PresentedAffinoidAlgebra.AffinoidPushout.finiteBanachPushout (K := K))

end Langlands.Analytic.SaturatedAtlasPresentation
