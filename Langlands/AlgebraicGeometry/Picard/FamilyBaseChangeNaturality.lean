import Langlands.AlgebraicGeometry.Picard.PoincareBaseChange
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs

/-! # Compatibility of ground-base and parameter pullback -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)

/-- The comparison of actual total spaces is natural in the parameter scheme. -/
@[reassoc]
lemma familyBaseChangeSpaceMap_naturality {T U : Over S'} (h : T ⟶ U) :
    (relativeSpace ((baseChange b).obj A).X.hom).map h ≫
        familyBaseChangeSpaceMap b A U =
      familyBaseChangeSpaceMap b A T ≫
        (relativeSpace A.X.hom).map ((Over.map b).map h) := by
  apply pullback.hom_ext <;>
    simp [relativeSpace, familyBaseChangeSpaceMap, Category.assoc]

/-- Ground-base pullback commutes with actual rigidified parameter pullback. -/
def familyBaseChangeNaturality {T U : Over S'} (h : T ⟶ U) :
    RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        ((Over.map b).map h) ⋙ familyBaseChange b A T ≅
      familyBaseChange b A U ⋙
        RigidifiedLineBundle.relativePullback ((baseChange b).obj A).X.hom
          (unitSection ((baseChange b).obj A)) (unitSection_comp _) h :=
  RigidifiedLineBundle.pullbackComp RigidifiedModule.pullbackCoherence
    ((relativeSpace A.X.hom).map ((Over.map b).map h)) h.left
    (familyBaseChangeSpaceMap b A T) (𝟙 T.left) _ _
    (by rw [← Category.assoc, relativeSection_familyBaseChangeSpaceMap]
        simpa only [Category.id_comp, Over.forget_map, Over.map_map_left] using
          ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).naturality
            ((Over.map b).map h)).symm) ≪≫
  RigidifiedLineBundle.pullbackCongr (familyBaseChangeSpaceMap_naturality b A h).symm
    (by simp) _ _ ≪≫
  (RigidifiedLineBundle.pullbackComp RigidifiedModule.pullbackCoherence
    (familyBaseChangeSpaceMap b A U) (𝟙 U.left)
    ((relativeSpace ((baseChange b).obj A).X.hom).map h) h.left _ _
    (by rw [← Category.assoc,
      ← (relativeSection ((baseChange b).obj A).X.hom
        (unitSection ((baseChange b).obj A)) (unitSection_comp _)).naturality]
        simp [Category.assoc])).symm

/-- A map into the actual base-changed parameter scheme, viewed over the old base. -/
def baseChangeParameterMate {T : Over S'} {P : Over S}
    (h : T ⟶ (Over.pullback b).obj P) : (Over.map b).obj T ⟶ P :=
  (Over.map b).map h ≫ baseChangeParameterMap b P

/-- Parameter maps correspond by the slice pullback adjunction. -/
def baseChangeParameterEquiv (T : Over S') (P : Over S) :
    (T ⟶ (Over.pullback b).obj P) ≃ ((Over.map b).obj T ⟶ P) :=
  ((Over.mapPullbackAdj b).homEquiv T P).symm

@[simp]
lemma baseChangeParameterEquiv_apply {T : Over S'} {P : Over S}
    (h : T ⟶ (Over.pullback b).obj P) :
    baseChangeParameterEquiv b T P h = baseChangeParameterMate b h := rfl

/-- Pulling back the explicitly base-changed family corresponds to the old mate map. -/
def baseChangeFamilyPullbackIso {T : Over S'} {P : Over S}
    (h : T ⟶ (Over.pullback b).obj P) :
    baseChangeFamily b A P ⋙
        RigidifiedLineBundle.relativePullback ((baseChange b).obj A).X.hom
          (unitSection ((baseChange b).obj A)) (unitSection_comp _) h ≅
      RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        (baseChangeParameterMate b h) ⋙ familyBaseChange b A T :=
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft
    (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
      (baseChangeParameterMap b P)) (familyBaseChangeNaturality b A h).symm ≪≫
  (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerRight
    (RigidifiedLineBundle.relativePullbackComp RigidifiedModule.pullbackCoherence
      A.X.hom (unitSection A) (unitSection_comp A)
      ((Over.map b).map h) (baseChangeParameterMap b P))
    (familyBaseChange b A T)

end Langlands.AbelianScheme
