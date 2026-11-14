import Langlands.Geometry.Analytic.EtaleSite

/-!
# Openness of étale morphisms of analytic spaces

This module states the consequence of Berkovich's Proposition 3.2.7 and
Definition 3.3.4 that an étale morphism is open.
-/

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

universe u v

/-- Every étale morphism of analytic spaces has an open underlying point map.
This is a statement, without a proof. -/
def EtaleOpenMapStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ ⦃U V : LocalizedCategory.{u, v, v} (K := K)⦄ (f : U ⟶ V),
    etale f → IsOpenMap (localizedSpaceFunctor.map f)

end Langlands.Analytic.SaturatedAtlasPresentation
