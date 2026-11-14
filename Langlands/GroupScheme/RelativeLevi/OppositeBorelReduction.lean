import Langlands.GroupScheme.RelativeLevi.OppositeBorelLocalConstruction
import Langlands.GroupScheme.RelativeLevi.OppositeBorelOverlap
import Langlands.GroupScheme.RelativeLevi.OppositeBorelGluing
import Langlands.GroupScheme.SubgroupFunctor.EtaleOverlapMatching

/-! # Reduction of the opposite Borel theorem to local presentation and Lie spreading -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Local dynamic presentation and Lie containment spreading suffice for the
unchanged global existence and uniqueness statement. -/
theorem relativeOppositeBorel_of_localPresentation_and_lieContainment
    (hpresentation : RelativeBorelDynamicPresentationStatement.{u})
    (hLie : RelativeParabolicLieContainmentStatement.{u}) :
    RelativeOppositeBorelStatement.{u} := by
  intro S G B i T t hG hT ht hmax hi hti
  have : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨𝒰, h𝒰⟩ :=
    exists_etaleLocal_oppositeBorel hpresentation i T t hG hT ht hmax hi hti
  choose C j hB hc hinter using h𝒰
  have hm : SubgroupFunctor.IsMatchingEtale 𝒰
      (fun a => SubgroupFunctor.range (j a)) := by
    apply SubgroupFunctor.isMatchingEtale_range_of_pairwiseOverlap_eq 𝒰 C j
    exact oppositeBorel_overlap_range_eq hLie i T t hG hT ht hmax hi 𝒰 C j hB hinter
  obtain ⟨C₀, j₀, hjB, _, hjinter⟩ :=
    exists_oppositeBorel_of_etaleLocal_matching i t 𝒰 C j hB hc hinter hm ht hti
  refine ⟨C₀, j₀, hjB, hjinter, ?_⟩
  intro C' j' hj' hj'inter
  exact oppositeRelativeBorel_range_eq (S := S) (G := G) (T := T)
    t i j' j₀ hLie hG hT ht hmax hi hj' hjB hj'inter hjinter

end Langlands.GroupScheme
