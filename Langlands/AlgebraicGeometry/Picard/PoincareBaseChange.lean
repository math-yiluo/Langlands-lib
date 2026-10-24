import Langlands.AlgebraicGeometry.Picard.FamilyBaseChange
import Langlands.AlgebraicGeometry.Picard.DualScheme

/-! # The actual base-changed Poincaré family -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)

/-- The projection of the base-changed parameter scheme, regarded over the old base. -/
def baseChangeParameterMap (P : Over S) :
    (Over.map b).obj ((Over.pullback b).obj P) ⟶ P :=
  Over.homMk (pullback.fst P.hom b) pullback.condition

/-- The actual map `P_{S'} ×_{S'} A_{S'} → P ×_S A`. -/
def baseChangeFamilySpaceMap (P : Over S) :
    (relativeSpace ((baseChange b).obj A).X.hom).obj ((Over.pullback b).obj P) ⟶
      (relativeSpace A.X.hom).obj P :=
  familyBaseChangeSpaceMap b A ((Over.pullback b).obj P) ≫
    (relativeSpace A.X.hom).map (baseChangeParameterMap b P)

@[reassoc (attr := simp)]
lemma baseChangeFamilySpaceMap_fst (P : Over S) :
    baseChangeFamilySpaceMap b A P ≫ pullback.fst P.hom A.X.hom =
      pullback.fst ((Over.pullback b).obj P).hom ((baseChange b).obj A).X.hom ≫
        pullback.fst P.hom b := by
  simp only [baseChangeFamilySpaceMap, Category.assoc, relativeSpace,
    Functor.comp_map, Over.forget_map, Over.pullback_map_left,
    pullback.lift_fst]
  exact familyBaseChangeSpaceMap_fst_assoc b A ((Over.pullback b).obj P)
    (pullback.fst P.hom b)

@[reassoc (attr := simp)]
lemma baseChangeFamilySpaceMap_snd (P : Over S) :
    baseChangeFamilySpaceMap b A P ≫ pullback.snd P.hom A.X.hom =
      pullback.snd ((Over.pullback b).obj P).hom ((baseChange b).obj A).X.hom ≫
        pullback.fst A.X.hom b := by
  simp only [baseChangeFamilySpaceMap, Category.assoc, relativeSpace,
    Functor.comp_map, Over.forget_map, Over.pullback_map_left,
    pullback.lift_snd]
  exact familyBaseChangeSpaceMap_snd b A ((Over.pullback b).obj P)

@[simp]
lemma relativeSection_baseChangeFamilySpaceMap (P : Over S) :
    (relativeSection ((baseChange b).obj A).X.hom
      (unitSection ((baseChange b).obj A)) (unitSection_comp _)).app
        ((Over.pullback b).obj P) ≫ baseChangeFamilySpaceMap b A P =
      pullback.fst P.hom b ≫
        (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app P := by
  rw [baseChangeFamilySpaceMap, ← Category.assoc,
    relativeSection_familyBaseChangeSpaceMap]
  exact ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).naturality
    (baseChangeParameterMap b P)).symm

/-- Change both the parameter scheme and the ground base of an actual family. -/
def baseChangeFamily (P : Over S) :
    RigidifiedFamily A P ⥤
      RigidifiedFamily ((baseChange b).obj A) ((Over.pullback b).obj P) :=
  RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
    (baseChangeParameterMap b P) ⋙ familyBaseChange b A ((Over.pullback b).obj P)

/-- The underlying line bundle is pullback along the actual total-space map. -/
def baseChangeFamilyForgetIso (P : Over S) :
    baseChangeFamily b A P ⋙ RigidifiedLineBundle.forget _ ≅
      RigidifiedLineBundle.forget _ ⋙ LineBundle.pullback (baseChangeFamilySpaceMap b A P) :=
  Functor.isoWhiskerLeft (RigidifiedLineBundle.forget _)
    (LineBundle.pullbackComp (familyBaseChangeSpaceMap b A ((Over.pullback b).obj P))
      ((relativeSpace A.X.hom).map (baseChangeParameterMap b P)))

/-- Pull back the chosen Poincaré family to the actual base-changed parameter scheme. -/
def poincareFamilyBaseChange (hA : HasDualScheme A) :
    RigidifiedFamily ((baseChange b).obj A) ((Over.pullback b).obj (dualScheme A hA)) :=
  (baseChangeFamily b A (dualScheme A hA)).obj (poincareFamily A hA)

/-- Its ordinary line bundle is the pullback of the original Poincaré line bundle
in the parameter-first convention. -/
def poincareFamilyBaseChangeForgetIso (hA : HasDualScheme A) :
    (RigidifiedLineBundle.forget _).obj (poincareFamilyBaseChange b A hA) ≅
      (LineBundle.pullback (baseChangeFamilySpaceMap b A (dualScheme A hA))).obj
        ((RigidifiedLineBundle.forget _).obj (poincareFamily A hA)) :=
  (baseChangeFamilyForgetIso b A (dualScheme A hA)).app (poincareFamily A hA)

end Langlands.AbelianScheme
