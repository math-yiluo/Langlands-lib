import Langlands.GroupScheme.SubgroupIntersection
import Langlands.CategoryTheory.GroupObjectDescent

/-! # Scheme-theoretic intersections inside a commutative subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {B : Scheme.{u}} {P R : GroupScheme B} {T : CommGroupScheme B}
variable (f : T.toGrp ⟶ P) (r : R ⟶ P) [Mono r.hom.hom]

/-- The pullback of a subgroup along a commutative group is commutative.
The mono hypothesis retains the given pullback group law. -/
def commutativeSubgroupIntersection : CommGroupScheme B where
  toGrp := subgroupIntersection f r
  comm := by
    let : Mono (subgroupIntersectionFst f r).hom.hom :=
      (subgroupIntersection_isPullback f r).mono_fst_of_mono
    exact Langlands.CategoryTheory.GroupObjectDescent.commMonObjOfMono
      (subgroupIntersectionFst f r).hom.hom

/-- The actual map of the commutative intersection into the commutative factor. -/
abbrev commutativeSubgroupIntersectionFst :
    (commutativeSubgroupIntersection f r).toGrp ⟶ T.toGrp :=
  subgroupIntersectionFst f r

/-- The actual map of the commutative intersection into the other subgroup. -/
abbrev commutativeSubgroupIntersectionSnd :
    (commutativeSubgroupIntersection f r).toGrp ⟶ R :=
  subgroupIntersectionSnd f r

/-- The two maps from the intersection have the same composite in the ambient group. -/
theorem commutativeSubgroupIntersection_condition :
    commutativeSubgroupIntersectionFst f r ≫ f =
      commutativeSubgroupIntersectionSnd f r ≫ r :=
  subgroupIntersection_condition f r

/-- The same commutative group scheme represents the intersection on every test scheme. -/
theorem range_commutativeSubgroupIntersection :
    SubgroupFunctor.range (commutativeSubgroupIntersectionFst f r ≫ f) =
      SubgroupFunctor.range f ⊓ SubgroupFunctor.range r :=
  range_subgroupIntersectionHom f r

/-- Closedness of the second input gives a closed inclusion into the commutative factor. -/
theorem isClosedSubgroup_commutativeSubgroupIntersectionFst
    (hr : IsClosedSubgroup r) :
    IsClosedSubgroup (commutativeSubgroupIntersectionFst f r) := by
  change IsClosedImmersion (subgroupIntersectionFst f r).hom.hom.left
  exact MorphismProperty.of_isPullback
    (subgroupIntersection_isPullback_scheme f r).flip hr

/-- Closedness of the first input gives a closed inclusion into the other factor. -/
theorem isClosedSubgroup_commutativeSubgroupIntersectionSnd
    (hf : IsClosedSubgroup f) :
    IsClosedSubgroup (commutativeSubgroupIntersectionSnd f r) := by
  change IsClosedImmersion (subgroupIntersectionSnd f r).hom.hom.left
  exact MorphismProperty.of_isPullback
    (subgroupIntersection_isPullback_scheme f r) hf

/-- The actual ambient map represents the intersection of two closed subgroup functors. -/
theorem isRepresentedBy_commutativeSubgroupIntersection
    (hf : IsClosedSubgroup f) (hr : IsClosedSubgroup r) :
    (SubgroupFunctor.range f ⊓ SubgroupFunctor.range r).IsRepresentedBy
      (commutativeSubgroupIntersectionFst f r ≫ f) :=
  isRepresentedBy_subgroupIntersectionHom hf hr

/-- Any compatible pair of group maps has a canonical map to this same intersection. -/
def commutativeSubgroupIntersectionLift {H : GroupScheme B}
    (a : H ⟶ T.toGrp) (b : H ⟶ R) (h : a ≫ f = b ≫ r) :
    H ⟶ (commutativeSubgroupIntersection f r).toGrp :=
  pullback.lift a b h

@[reassoc (attr := simp)]
theorem commutativeSubgroupIntersectionLift_fst {H : GroupScheme B}
    (a : H ⟶ T.toGrp) (b : H ⟶ R) (h : a ≫ f = b ≫ r) :
    commutativeSubgroupIntersectionLift f r a b h ≫
      commutativeSubgroupIntersectionFst f r = a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem commutativeSubgroupIntersectionLift_snd {H : GroupScheme B}
    (a : H ⟶ T.toGrp) (b : H ⟶ R) (h : a ≫ f = b ≫ r) :
    commutativeSubgroupIntersectionLift f r a b h ≫
      commutativeSubgroupIntersectionSnd f r = b :=
  pullback.lift_snd _ _ _

/-- A map to the intersection is determined by its two projections. -/
theorem commutativeSubgroupIntersection_hom_ext {H : GroupScheme B}
    {a b : H ⟶ (commutativeSubgroupIntersection f r).toGrp}
    (hT : a ≫ commutativeSubgroupIntersectionFst f r =
      b ≫ commutativeSubgroupIntersectionFst f r)
    (hR : a ≫ commutativeSubgroupIntersectionSnd f r =
      b ≫ commutativeSubgroupIntersectionSnd f r) : a = b :=
  pullback.hom_ext hT hR

end Langlands.GroupScheme
