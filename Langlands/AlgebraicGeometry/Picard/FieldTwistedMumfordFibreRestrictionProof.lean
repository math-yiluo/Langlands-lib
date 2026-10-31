import Langlands.AlgebraicGeometry.Picard.FieldTwistedMumfordFibreRestrictionStatement
import Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroReduction
import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof

/-! # Both field fibre restrictions of a twisted ordinary Mumford tensor

The theorem `fieldTwistedMumfordFibreRestriction` proves
`FieldTwistedMumfordFibreRestrictionStatement`. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme.FieldTwistedMumford

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AbelianScheme.MumfordPicardZero (tensorIsoOf pullbackTensorIso pullbackCompIso
  constantIso)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Coordinates

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))
  (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X)

/-- The constant endomorphism of `A` with value `x`. -/
abbrev constPoint : A.X ⟶ A.X := Over.mkIdTerminal.from A.X ≫ x

/-- The first fibre inclusion `(c_x, id) : A → A ×_K A`. -/
abbrev firstLift : A.X.left ⟶ pullback A.X.hom A.X.hom :=
  pullback.lift (A.X.hom ≫ x.left) (𝟙 A.X.left) (by simp [Category.assoc, Over.w x])

/-- The second fibre inclusion `(id, c_x) : A → A ×_K A`. -/
abbrev secondLift : A.X.left ⟶ pullback A.X.hom A.X.hom :=
  pullback.lift (𝟙 A.X.left) (A.X.hom ≫ x.left) (by simp [Category.assoc, Over.w x])

lemma constPoint_left : (constPoint A x).left = A.X.hom ≫ x.left := by
  rw [Over.comp_left, Over.mkIdTerminal_from_left]

lemma firstLift_fst : firstLift A x ≫ pullback.fst A.X.hom A.X.hom = (constPoint A x).left :=
  (pullback.lift_fst _ _ _).trans (constPoint_left A x).symm

lemma firstLift_snd : firstLift A x ≫ pullback.snd A.X.hom A.X.hom = 𝟙 A.X.left :=
  pullback.lift_snd _ _ _

lemma secondLift_fst : secondLift A x ≫ pullback.fst A.X.hom A.X.hom = 𝟙 A.X.left :=
  pullback.lift_fst _ _ _

lemma secondLift_snd :
    secondLift A x ≫ pullback.snd A.X.hom A.X.hom = (constPoint A x).left :=
  (pullback.lift_snd _ _ _).trans (constPoint_left A x).symm

/-- The first fibre inclusion as a morphism over the base. -/
def firstLiftOver : A.X ⟶ mumfordProduct A :=
  Over.homMk (firstLift A x) (by
    change firstLift A x ≫ pullback.fst A.X.hom A.X.hom ≫ A.X.hom = A.X.hom
    rw [← Category.assoc, firstLift_fst]
    exact Over.w (constPoint A x))

/-- The second fibre inclusion as a morphism over the base. -/
def secondLiftOver : A.X ⟶ mumfordProduct A :=
  Over.homMk (secondLift A x) (by
    change secondLift A x ≫ pullback.fst A.X.hom A.X.hom ≫ A.X.hom = A.X.hom
    rw [← Category.assoc, secondLift_fst, Category.id_comp])

lemma firstLiftOver_first : firstLiftOver A x ≫ mumfordFirst A = constPoint A x :=
  Over.OverMorphism.ext (firstLift_fst A x)

lemma firstLiftOver_second : firstLiftOver A x ≫ mumfordSecond A = 𝟙 A.X :=
  Over.OverMorphism.ext (firstLift_snd A x)

lemma secondLiftOver_first : secondLiftOver A x ≫ mumfordFirst A = 𝟙 A.X :=
  Over.OverMorphism.ext (secondLift_fst A x)

lemma secondLiftOver_second : secondLiftOver A x ≫ mumfordSecond A = constPoint A x :=
  Over.OverMorphism.ext (secondLift_snd A x)

/-- On `(c_x, id)`, addition is translation by `x`. -/
lemma firstLift_addition :
    firstLift A x ≫ mumfordAddition A = (GroupScheme.translation A.toGrp x).left := by
  have h : firstLiftOver A x ≫ (mumfordFirst A * mumfordSecond A) =
      GroupScheme.translation A.toGrp x := by
    rw [MonObj.comp_mul, firstLiftOver_first, firstLiftOver_second]
    rfl
  exact congrArg CommaMorphism.left h

/-- On `(id, c_x)`, addition is translation by `x`, by commutativity of `A`. -/
lemma secondLift_addition :
    secondLift A x ≫ mumfordAddition A = (GroupScheme.translation A.toGrp x).left := by
  have h : secondLiftOver A x ≫ (mumfordFirst A * mumfordSecond A) =
      GroupScheme.translation A.toGrp x := by
    rw [MonObj.comp_mul, secondLiftOver_first, secondLiftOver_second, mul_comm]
    rfl
  exact congrArg CommaMorphism.left h

end Coordinates

section Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})

/-- Pullback distributes over a left-nested fourfold tensor product. -/
def pullbackTensorFourIso {X Y : Scheme.{u}} (f : Y ⟶ X) (a b c d : X.Modules) :
    (Scheme.Modules.pullback f).obj (tensorObj (tensorObj (tensorObj a b) c) d) ≅
      tensorObj (tensorObj (tensorObj ((Scheme.Modules.pullback f).obj a)
        ((Scheme.Modules.pullback f).obj b)) ((Scheme.Modules.pullback f).obj c))
        ((Scheme.Modules.pullback f).obj d) :=
  pullbackTensorIso preservation f _ d ≪≫
    tensorIsoOf (pullbackTensorIso preservation f _ c ≪≫
      tensorIsoOf (pullbackTensorIso preservation f a b) (Iso.refl _)) (Iso.refl _)

/-- Successive pullbacks along a factorization of the identity give back the module. -/
def pullbackIdFactorIso {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ X) (w : f ≫ g = 𝟙 X)
    (M : X.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ≅ M :=
  (pullbackCompIso f g (𝟙 X) w M).symm ≪≫ (Scheme.Modules.pullbackId X).app M

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))
  (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X)

/-- Successive pullbacks along a factorization of the constant map `c_x` are trivial,
by unconditional triviality of line bundles over a field. -/
def pullbackConstFactorIso {Y : Scheme.{u}} (f : A.X.left ⟶ Y) (g : Y ⟶ A.X.left)
    (w : f ≫ g = (constPoint A x).left) (N : LineBundle A.X.left) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N.obj) ≅
      structureSheaf A.X.left :=
  (pullbackCompIso f g _ w N.obj).symm ≪≫ constantIso fieldLineBundleTriviality A.toGrp x N

/-- The underlying module comparison for the restriction along `(c_x, id)`. -/
def firstRestrictionIso (L N R : LineBundle A.X.left) :
    (Scheme.Modules.pullback (firstLift A x)).obj
      (tensorObj (tensorObj (tensorObj
        ((Scheme.Modules.pullback (mumfordAddition A)).obj L.obj)
        ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj N.obj))
        ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj N.obj))
        ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj R.obj)) ≅
      tensorObj (tensorObj
        ((Scheme.Modules.pullback (GroupScheme.translation A.toGrp x).left).obj L.obj) N.obj)
        R.obj :=
  pullbackTensorFourIso preservation (firstLift A x) _ _ _ _ ≪≫
    tensorIsoOf
      (tensorIsoOf
        (tensorIsoOf (pullbackCompIso _ _ _ (firstLift_addition A x) L.obj).symm
            (pullbackConstFactorIso A x _ _ (firstLift_fst A x) N) ≪≫
          tensorRightUnitor _)
        (pullbackIdFactorIso _ _ (firstLift_snd A x) N.obj))
      (pullbackIdFactorIso _ _ (firstLift_snd A x) R.obj)

/-- The underlying module comparison for the restriction along `(id, c_x)`. -/
def secondRestrictionIso (L N R : LineBundle A.X.left) :
    (Scheme.Modules.pullback (secondLift A x)).obj
      (tensorObj (tensorObj (tensorObj
        ((Scheme.Modules.pullback (mumfordAddition A)).obj L.obj)
        ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj N.obj))
        ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj N.obj))
        ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj R.obj)) ≅
      tensorObj
        ((Scheme.Modules.pullback (GroupScheme.translation A.toGrp x).left).obj L.obj) N.obj :=
  pullbackTensorFourIso preservation (secondLift A x) _ _ _ _ ≪≫
    tensorIsoOf
      (tensorIsoOf
        (tensorIsoOf (pullbackCompIso _ _ _ (secondLift_addition A x) L.obj).symm
          (pullbackIdFactorIso _ _ (secondLift_fst A x) N.obj))
        (pullbackConstFactorIso A x _ _ (secondLift_snd A x) N) ≪≫
        tensorRightUnitor _)
      (pullbackConstFactorIso A x _ _ (secondLift_snd A x) R) ≪≫
    tensorRightUnitor _

end Modules

end Langlands.AbelianScheme.FieldTwistedMumford

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard FieldTwistedMumford

/-- Both fibre restrictions of the twisted ordinary Mumford tensor over a field. -/
theorem fieldTwistedMumfordFibreRestriction :
    FieldTwistedMumfordFibreRestrictionStatement.{u} := by
  intro preservation K _ A L N R Z p1 p2 m Q x i1 i2 D
  exact ⟨⟨ObjectProperty.isoMk _ (firstRestrictionIso preservation A x L N R)⟩,
    ⟨ObjectProperty.isoMk _ (secondRestrictionIso preservation A x L N R)⟩⟩

end Langlands.AbelianScheme
