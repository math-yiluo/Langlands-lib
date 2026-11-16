import Langlands.GroupScheme.Reductive.FibreLocusComparisons
import Langlands.GroupScheme.Reductive.IdentityComponentLocusOpenDescent
import Langlands.GroupScheme.Reductive.IdentityComponentSemisimpleLocusStatement

/-! # Open descent for the semisimple identity-component locus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

local instance semisimpleDescent_smooth_pullback {S T : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] (b : T ⟶ S) : Smooth ((baseChange b).obj G).X.hom :=
  inferInstanceAs (Smooth (Limits.pullback.snd G.X.hom b))

local instance semisimpleDescent_affine_pullback {S T : Scheme.{u}} (G : GroupScheme S)
    [IsAffineHom G.X.hom] (b : T ⟶ S) : IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

variable {S : Scheme.{u}} (G : GroupScheme S)
  [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- An open neighbourhood contained in the actual semisimple identity-component locus. -/
structure IdentityComponentSemisimpleOpenNeighbourhood (s : S) where
  neighbourhood : S.Opens
  mem_neighbourhood : s ∈ neighbourhood
  subset_locus : (neighbourhood : Set S) ⊆ identityComponentSemisimpleLocus G

/-- Images under open maps descend good semisimple neighbourhoods. -/
def identityComponentSemisimpleOpenNeighbourhood_of_openMap
    {T : Scheme.{u}} (b : T ⟶ S) (hb : IsOpenMap b)
    (t : T) {U : Set T} (hU : IsOpen U) (ht : t ∈ U)
    (hss : U ⊆ identityComponentSemisimpleLocus ((baseChange b).obj G)) :
    IdentityComponentSemisimpleOpenNeighbourhood G (b t) where
  neighbourhood := ⟨b '' U, hb U hU⟩
  mem_neighbourhood := ⟨t, ht, rfl⟩
  subset_locus := by
    rintro _ ⟨x, hx, rfl⟩
    have h := hss hx
    rwa [identityComponentSemisimpleLocus_baseChange] at h

end Langlands.GroupScheme
