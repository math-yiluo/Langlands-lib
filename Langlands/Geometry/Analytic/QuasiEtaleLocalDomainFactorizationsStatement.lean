import Langlands.Geometry.Analytic.QuasiEtaleDomainLocality

/-! # Statement: quasi-étale maps have domain–étale factorizations through every point -/

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory

/-- Statement: every quasi-étale arrow of the localized category, with an arbitrary source
that is not assumed Hausdorff, has at each source point finitely many analytic domains
containing that point whose union is a neighbourhood of it, each with a domain–étale
factorization of the restricted arrow. -/
def QuasiEtaleLocalDomainFactorizationsStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ {U X : LocalizedCategory.{u, v, v} (K := K)} (f : U ⟶ X),
    quasiEtale f → HasLocalDomainEtaleFactorizations f

end Langlands.Analytic.SaturatedAtlasPresentation
