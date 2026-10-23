import Langlands.Representation.CompactCoefficient.AmbientProjector
import Langlands.Representation.Filtration.SubquotientAlgebraProof

/-! Actual subgroup restriction as a functor, with its elementary subquotient laws. -/

noncomputable section

open CategoryTheory

namespace Langlands.SmoothRep

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The actual subgroup-restriction functor, retaining carriers and linear maps. -/
def restrictSubgroupFunctor (N : Subgroup G) :
    SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uG, uV} ℂ N where
  obj := restrictSubgroup N
  map f := ofHom (restrictSubgroupMap N (hom f))
  map_id A := by rfl
  map_comp f g := by rfl

/-- Restriction preserves actual smooth subquotients because its underlying
linear maps, and hence their injectivity and surjectivity, are unchanged. -/
theorem IsSubquotient.restrictSubgroup (N : Subgroup G)
    {A D : SmoothRep.{0, uG, uV} ℂ G} (h : IsSubquotient D A) :
    IsSubquotient (restrictSubgroup N D) (restrictSubgroup N A) := by
  obtain ⟨C, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp h
  exact isSubquotient_iff_exists.mpr
    ⟨SmoothRep.restrictSubgroup N C, (restrictSubgroupFunctor N).map i,
      (restrictSubgroupFunctor N).map q, hi, hq⟩

/-- Every actual invariant subspace of the restriction of a subquotient is
itself an actual subquotient of the restricted ambient representation. -/
theorem restricted_subrepresentation_isSubquotient (N : Subgroup G)
    {A D : SmoothRep.{0, uG, uV} ℂ G} (h : IsSubquotient D A)
    (W : Subrepresentation (restrictSubgroup N D).representation) :
    IsSubquotient (subrepresentation (restrictSubgroup N D) W)
      (restrictSubgroup N A) := by
  exact Langlands.smoothSubquotientTransitivity ℂ N _ _ _
    (subrepresentation_isSubrepresentation W |>.isSubquotient)
    (h.restrictSubgroup N)

/-- Excluding a single actual subrepresentation of the restricted candidate
from the restricted ambient representation excludes the ambient subquotient. -/
theorem not_isSubquotient_of_restricted_subrepresentation (N : Subgroup G)
    {A D : SmoothRep.{0, uG, uV} ℂ G}
    (W : Subrepresentation (restrictSubgroup N D).representation)
    (hW : ¬ IsSubquotient (subrepresentation (restrictSubgroup N D) W)
      (restrictSubgroup N A)) :
    ¬ IsSubquotient D A :=
  fun h => hW (restricted_subrepresentation_isSubquotient N h W)

end Langlands.SmoothRep
