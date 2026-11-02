import Langlands.AlgebraicGeometry.Picard.CoherentFamilyRankOneOpen
import Langlands.CategoryTheory.Sites.PseudofunctorHomLift

/-! # Actual coherent-family points factor through the rank-one open -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.Picard

open CoherentSheaves Langlands.CategoryTheory.PseudofunctorPointFiber

variable {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f]
  {U : Over S} (M : FamilyGroupoid f U)

instance familyRankOneInclusion_mono : Mono (familyRankOneInclusion f M) := by
  dsimp only [familyRankOneInclusion]
  infer_instance

instance familyRankOneBase_locallyOfFiniteType [LocallyOfFiniteType U.hom] :
    LocallyOfFiniteType (familyRankOneBase f M).hom := by
  change LocallyOfFiniteType ((familyRankOneOpen f M).ι ≫ U.hom)
  infer_instance

variable [LocallyOfFinitePresentation f]
  {T : Over S} (N : FamilyGroupoid f T) (hN : IsLocallyFreeRankOne N.of.obj)
  (Z : Over T)

include hN

omit [UniversallyClosed f] [LocallyOfFinitePresentation f] in
/-- The actual point isomorphism makes the atlas family rank one after pullback. -/
lemma familyRankOnePoint_isLocallyFreeRankOne
    (x : Points (FamilyGroupoid.pseudofunctor f) M N Z) :
    IsLocallyFreeRankOne (((FamilyGroupoid.pullback f x.1).obj M).of.obj) := by
  have h := hN.pullback ((relativeSpace f).map Z.hom)
  exact h.of_iso ((FamilyGroupoid.forget f Z.left).mapIso x.2).symm

/-- The actual base map underlying every point factors through the rank-one open. -/
def familyRankOnePointLift
    (x : Points (FamilyGroupoid.pseudofunctor f) M N Z) :
    Z.left ⟶ familyRankOneBase f M :=
  familyRankOneLift f M x.1 (familyRankOnePoint_isLocallyFreeRankOne f M N hN Z x)

@[reassoc (attr := simp)]
lemma familyRankOnePointLift_fac
    (x : Points (FamilyGroupoid.pseudofunctor f) M N Z) :
    familyRankOnePointLift f M N hN Z x ≫ familyRankOneInclusion f M = x.1 :=
  familyRankOneLift_fac f M x.1 _

/-- Monicity gives uniqueness of the actual point factorization. -/
lemma familyRankOnePointLift_uniq
    (x : Points (FamilyGroupoid.pseudofunctor f) M N Z)
    (a : Z.left ⟶ familyRankOneBase f M)
    (ha : a ≫ familyRankOneInclusion f M = x.1) :
    a = familyRankOnePointLift f M N hN Z x :=
  familyRankOneLift_uniq f M x.1 _ a ha

/-- The same actual factorization is available after the explicit hom lift. -/
def familyRankOneHomLiftPointLift
    (x : Points
      (Langlands.CategoryTheory.PseudofunctorHomLift.homLift.{u + 1}
        (FamilyGroupoid.pseudofunctor f))
      (ULiftHom.objUp.{u + 1, u + 1} M) (ULiftHom.objUp.{u + 1, u + 1} N) Z) :
    Z.left ⟶ familyRankOneBase f M :=
  familyRankOnePointLift f M N hN Z
    ((Langlands.CategoryTheory.PseudofunctorHomLift.pointsEquiv.{u + 1}
      (F := FamilyGroupoid.pseudofunctor f) M N Z) x).down

@[reassoc (attr := simp)]
lemma familyRankOneHomLiftPointLift_fac
    (x : Points
      (Langlands.CategoryTheory.PseudofunctorHomLift.homLift.{u + 1}
        (FamilyGroupoid.pseudofunctor f))
      (ULiftHom.objUp.{u + 1, u + 1} M) (ULiftHom.objUp.{u + 1, u + 1} N) Z) :
    familyRankOneHomLiftPointLift f M N hN Z x ≫ familyRankOneInclusion f M = x.1 :=
  familyRankOnePointLift_fac f M N hN Z _

end Langlands.AlgebraicGeometry.Picard
