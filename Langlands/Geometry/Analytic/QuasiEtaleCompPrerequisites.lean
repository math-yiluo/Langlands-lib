import Langlands.Geometry.Analytic.QuasiEtaleStabilityStatement
import Langlands.Geometry.Analytic.QuasiEtaleLocalDomainFactorizationsStatement

/-! # Statements: an ingredient of the composition of quasi-étale morphisms -/

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory

/-- Statement: an étale morphism into an analytic domain `D` of `W`, followed
by the inclusion of `D` into `W`, is quasi-étale. -/
def EtaleDomainQuasiEtaleStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ {E W : LocalizedCategory.{u, v, v} (K := K)} (D : (presentationOf W).AnalyticDomain)
    (e : E ⟶ domainObj W D), etale e → quasiEtale (e ≫ domainι W D)

/-- Statement: local domain–étale factorizations of quasi-étale morphisms
(`QuasiEtaleLocalDomainFactorizationsStatement`) and the statement above imply
that quasi-étale morphisms are stable under composition. -/
def QuasiEtaleCompReductionStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  QuasiEtaleLocalDomainFactorizationsStatement.{u, v} K →
    EtaleDomainQuasiEtaleStatement.{u, v} K → QuasiEtaleCompStatement.{u, v} K

end Langlands.Analytic.SaturatedAtlasPresentation
