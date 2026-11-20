import Langlands.Geometry.Analytic.InvariantAnalyticDomains

/-! # Statement: an analytic space partitioned into open domains is their disjoint union -/

universe u v z

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic.SaturatedAtlasPresentation

/-- Statement: if the underlying space of an analytic space `Y` is the disjoint union of a
family of open subsets `U j`, then `Y`, with the canonical morphisms `ν_j : U_j → Y` of the
open domains `U_j`, is a coproduct of these domains in the localized category of analytic
spaces. -/
def OpenPartitionCoproductStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {J : Type z}
    (Y : LocalizedCategory.{u, max z v, max z v} (K := K))
    (U : J → Set (presentationOf Y).presentation.space) (hU : ∀ j, IsOpen (U j)),
    Pairwise (fun i j => Disjoint (U i) (U j)) → (∀ y, ∃ j, y ∈ U j) →
      Nonempty (IsColimit (Cofan.mk Y fun j =>
        domainι Y ((presentationOf Y).openDomain (U j) (hU j))))

end Langlands.Analytic.SaturatedAtlasPresentation
