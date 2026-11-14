import Langlands.GroupScheme.RelativeLevi.OppositeBorelReduction

/-! # A chosen opposite Borel from local presentation and Lie spreading -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeOppositeBorelConstruction

variable (hpresentation : RelativeBorelDynamicPresentationStatement.{u})
    (hLie : RelativeParabolicLieContainmentStatement.{u})
    (S : Scheme.{u}) (G B : GroupScheme S) (i : B ⟶ G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G)
    (hG : IsReductive G) (hT : RelativeTorus.IsTorus T.toGrp)
    (ht : IsClosedSubgroup t) (hmax : IsFibrewiseMaximalTorus t)
    (hi : IsRelativeBorelSubgroup i)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)

/-- The chosen global opposite Borel scheme, conditional on the two
explicit local geometric inputs. -/
def group : GroupScheme S :=
  Classical.choose
    (relativeOppositeBorel_of_localPresentation_and_lieContainment hpresentation hLie
      S G B i T t hG hT ht hmax hi hti)

/-- The inclusion of the chosen opposite Borel into the original ambient group. -/
def hom : group hpresentation hLie S G B i T t hG hT ht hmax hi hti ⟶ G :=
  Classical.choose (Classical.choose_spec
    (relativeOppositeBorel_of_localPresentation_and_lieContainment hpresentation hLie
      S G B i T t hG hT ht hmax hi hti))

/-- The chosen inclusion is relative Borel, meets the original Borel in the
given torus, and has the unique all-test image with these properties. -/
theorem spec :
    IsRelativeBorelSubgroup (hom hpresentation hLie S G B i T t hG hT ht hmax hi hti) ∧
      SubgroupFunctor.range (hom hpresentation hLie S G B i T t hG hT ht hmax hi hti) ⊓
          SubgroupFunctor.range i = SubgroupFunctor.range t ∧
        ∀ (C : GroupScheme S) (j : C ⟶ G), IsRelativeBorelSubgroup j →
          SubgroupFunctor.range j ⊓ SubgroupFunctor.range i = SubgroupFunctor.range t →
            SubgroupFunctor.range j =
              SubgroupFunctor.range
                (hom hpresentation hLie S G B i T t hG hT ht hmax hi hti) :=
  Classical.choose_spec (Classical.choose_spec
    (relativeOppositeBorel_of_localPresentation_and_lieContainment hpresentation hLie
      S G B i T t hG hT ht hmax hi hti))

end Langlands.GroupScheme.RelativeOppositeBorelConstruction
