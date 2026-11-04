import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Reductive.Basic

/-! # Finite fppf restrictions to commutative closed subgroups -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {B : Scheme.{u}} {C G : GroupScheme B}
  {T S : CommGroupScheme B}

/-- A map between closed subgroups which is the restriction of a finite map is finite. -/
theorem isFinite_of_closed_subgroup_restriction
    {π : C ⟶ G} (hπ : IsFinite π.hom.hom.left)
    {j : T.toGrp ⟶ C} (hj : IsClosedSubgroup j)
    {i : S.toGrp ⟶ G} (hi : IsClosedSubgroup i)
    (f : T ⟶ S) (hcomm : j ≫ π = CommGroupScheme.groupHom f ≫ i) :
    IsFinite (CommGroupScheme.groupHom f).hom.hom.left := by
  have : IsFinite π.hom.hom.left := hπ
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsClosedImmersion i.hom.hom.left := hi
  have hsquare : j.hom.hom.left ≫ π.hom.hom.left =
      (CommGroupScheme.groupHom f).hom.hom.left ≫ i.hom.hom.left :=
    congrArg (fun q : T.toGrp ⟶ G => q.hom.hom.left) hcomm
  have : IsFinite ((CommGroupScheme.groupHom f).hom.hom.left ≫ i.hom.hom.left) := by
    rw [← hsquare]
    infer_instance
  exact IsFinite.of_comp _ i.hom.hom.left

/-- An fppf restriction of a finite map to commutative closed subgroups is a central
isogeny, with centrality asserted for the full scheme-theoretic kernel. -/
theorem isCentralIsogeny_of_fppf_closed_subgroup_restriction
    {π : C ⟶ G} (hπ : IsFinite π.hom.hom.left)
    {j : T.toGrp ⟶ C} (hj : IsClosedSubgroup j)
    {i : S.toGrp ⟶ G} (hi : IsClosedSubgroup i)
    (f : T ⟶ S) (hcomm : j ≫ π = CommGroupScheme.groupHom f ≫ i)
    (hflat : Flat (CommGroupScheme.groupHom f).hom.hom.left)
    (hsurj : Surjective (CommGroupScheme.groupHom f).hom.hom.left)
    (hlfp : LocallyOfFinitePresentation (CommGroupScheme.groupHom f).hom.hom.left) :
    IsCentralIsogeny (CommGroupScheme.groupHom f) := by
  refine ⟨⟨isFinite_of_closed_subgroup_restriction hπ hj hi f hcomm, hflat, hsurj⟩,
    hlfp, ?_⟩
  intro U x U' a y
  exact Commute.all _ _

end Langlands.GroupScheme
