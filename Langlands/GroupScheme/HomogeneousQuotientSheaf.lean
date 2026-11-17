import Langlands.GroupScheme.HomogeneousQuotientBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability

/-! # The canonical sheaf of homogeneous cosets and local scheme models -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient
open Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

namespace Langlands.GroupScheme.HomogeneousQuotientSheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {G H : GroupScheme S} (i : H ⟶ G) [Mono i.hom.hom]

/-- The canonical etale sheaf of right cosets. -/
abbrev presheaf : Presheaf S :=
  (quotientSheaf (arrowSpace i) (source i) (target i) (isEquivalenceRelation i)).obj

/-- The canonical quotient transformation. -/
abbrev projection : (schemeYoneda S).obj G.X ⟶ presheaf i :=
  quotientMap (arrowSpace i) (source i) (target i) (isEquivalenceRelation i)

variable [LocallyOfFiniteType G.X.hom] (hH : Smooth H.X.hom)

/-- Smooth subgroup cosets form an actual fppf sheaf. -/
def sheaf : FppfSheaf S :=
  ⟨presheaf i, (smoothRelationQuotient S G.X (arrowSpace i) (source i) (target i)
    (isEquivalenceRelation i) (hasSmoothProjections i hH) inferInstance).1⟩

include hH in
/-- The canonical quotient transformation is smooth. -/
theorem smooth_projection : IsSmooth (projection i) :=
  (smoothRelationQuotient S G.X (arrowSpace i) (source i) (target i)
    (isEquivalenceRelation i) (hasSmoothProjections i hH) inferInstance).2.2.2.1

include hH in
/-- The canonical quotient transformation is surjective. -/
theorem surjective_projection : IsSurjective (projection i) :=
  (smoothRelationQuotient S G.X (arrowSpace i) (source i) (target i)
    (isEquivalenceRelation i) (hasSmoothProjections i hH) inferInstance).2.2.2.2.1

omit [LocallyOfFiniteType G.X.hom] in
/-- The kernel of the quotient transformation is the full scheme-theoretic coset relation. -/
theorem projection_eq_iff (T : Over S) (g h : T ⟶ G.X) :
    (projection i).app (op T) ⟨g⟩ = (projection i).app (op T) ⟨h⟩ ↔
      g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T :=
  (quotientMap_eq_iff (arrowSpace i) (source i) (target i) (isEquivalenceRelation i) _ _).trans
    (relation_iff i T g h)

include hH in
/-- The quotient transformation is locally surjective for the actual fppf topology. -/
theorem locallySurjective_projection :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) (projection i) := by
  apply isLocallySurjective_of_fppf_projections (projection i) (smooth_projection i hH).representable
  intro T V g b p h
  have := (smooth_projection i hH).projection g b p h
  exact ⟨inferInstance, inferInstance, (surjective_projection i hH).projection g b p h⟩

variable {S' : Scheme.{u}} (b : S' ⟶ S)

omit [LocallyOfFiniteType G.X.hom] in
/-- On a base-changed group, the restricted quotient has the base-changed coset fibers. -/
theorem restrict_projection_eq_iff (T : Over S')
    (g h : T ⟶ ((GroupScheme.baseChange b).obj G).X) :
    (restrictAtlas b (projection i)).app (op T) ⟨g⟩ =
      (restrictAtlas b (projection i)).app (op T) ⟨h⟩ ↔
        g⁻¹ * h ∈ (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)).carrier T := by
  change (projection i).app (op ((Over.map b).obj T))
      ⟨baseChangePointsEquiv b G T g⟩ =
    (projection i).app (op ((Over.map b).obj T))
      ⟨baseChangePointsEquiv b G T h⟩ ↔ _
  rw [projection_eq_iff, SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.mem_baseChange,
    map_mul, map_inv]

include hH in
/-- Every supplied quotient of the base-changed subgroup represents the restriction
of the original canonical quotient sheaf. -/
theorem representableBy_baseChange
    (Q : HomogeneousQuotient ((GroupScheme.baseChange b).map i)) :
    Nonempty (((Over.map b).op ⋙ presheaf i).RepresentableBy Q.scheme) := by
  let F : FppfSheaf S' :=
    (Scheme.fppfTopology.overMapPullback (Type (u + 1)) b).obj (sheaf i hH)
  have ha : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S')
      (restrictAtlas b (projection i)) := by
    apply isLocallySurjective_of_fppf_projections _
      (relative_restrictAtlas (g := b) (@Smooth) (smooth_projection i hH)).rep
    intro T V g c p h
    have hp : Smooth p.left :=
      (relative_restrictAtlas (g := b) (@Smooth) (smooth_projection i hH)).2 g c p h
    have hs : Surjective p.left :=
      (relative_restrictAtlas (g := b) (@Surjective) (surjective_projection i hH)).2 g c p h
    exact ⟨inferInstance, inferInstance, hs⟩
  let : Smooth Q.projection.left := Q.smooth_projection
  let : Surjective Q.projection.left := Q.surjective_projection
  exact representableBy_of_fppf_quotient (F := F) (restrictAtlas b (projection i)) Q.projection
    ha (fun T g h => (restrict_projection_eq_iff i b T g h).trans (Q.fibers T g h).symm)

end Langlands.GroupScheme.HomogeneousQuotientSheaf
