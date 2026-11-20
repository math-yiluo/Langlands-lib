import Langlands.Geometry.Analytic.QuasiEtaleSite
import Langlands.Geometry.Analytic.InvariantAnalyticDomains

/-! # Statement: quasi-étale morphisms restrict to quasi-étale morphisms over open domains -/

universe u v

open CategoryTheory

namespace Langlands.Analytic.SaturatedAtlasPresentation

/-- Statement (Berkovich 1994, Lemma 3.1(i), base change along an open immersion, for a
Hausdorff source): if `f : Y → Z` is quasi-étale and `V` is an open subset of `Z`, then the
restriction `f⁻¹(V) → V` of `f` to the open domains `f⁻¹(V)` of `Y` and `V` of `Z` is
quasi-étale. -/
def QuasiEtaleOpenRestrictionStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {Y Z : LocalizedCategory.{u, v, v} (K := K)} [T2Space (localizedSpaceFunctor.obj Y)]
    (f : Y ⟶ Z), quasiEtale f →
      ∀ (V : Set (presentationOf Z).presentation.space) (hV : IsOpen V),
        quasiEtale (domainRestrict
          ((presentationOf Y).openDomain (localizedSpaceFunctor.map f ⁻¹' V)
            (hV.preimage (localizedSpaceFunctor.map f).hom.continuous))
          ((presentationOf Z).openDomain V hV) f fun _ hx => hx)

end Langlands.Analytic.SaturatedAtlasPresentation
