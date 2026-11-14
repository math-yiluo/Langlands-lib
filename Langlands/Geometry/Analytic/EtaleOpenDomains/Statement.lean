import Langlands.Geometry.Analytic.EtaleSite
import Langlands.Geometry.Analytic.InvariantAnalyticDomains

/-! # Étaleness of canonical inclusions of open analytic domains -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The canonical inclusion of each open analytic domain of `X` is étale for
the published all-affinoid-pieces definition of étaleness. -/
def EtaleOpenDomainStatement (X : LocalizedCategory.{u, v, v} (K := K)) : Prop :=
  ∀ (U : Set (localizedSpaceFunctor.obj X)) (hU : IsOpen U),
    etale (domainι X ((presentationOf X).openDomain U hU))

end Langlands.Analytic.SaturatedAtlasPresentation
