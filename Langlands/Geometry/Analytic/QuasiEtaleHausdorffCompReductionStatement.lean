import Langlands.Geometry.Analytic.QuasiEtaleCompPrerequisites
import Langlands.Geometry.Analytic.QuasiEtaleHausdorffStabilityStatement

/-! # Statement: composition of quasi-étale morphisms with Hausdorff sources from one premise -/

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

/-- Statement: if an étale morphism into an analytic domain, followed by the inclusion of the
domain, is always quasi-étale (`EtaleDomainQuasiEtaleStatement`), then quasi-étale morphisms
`f : A ⟶ B` and `g : B ⟶ C` with Hausdorff underlying spaces of `A` and `B` compose to a
quasi-étale morphism (`QuasiEtaleHausdorffCompStatement`). -/
def QuasiEtaleHausdorffCompReductionStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  EtaleDomainQuasiEtaleStatement.{u, v} K → QuasiEtaleHausdorffCompStatement.{u, v} K

end Langlands.Analytic.SaturatedAtlasPresentation
