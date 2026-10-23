import Langlands.AlgebraicGeometry.Picard.RelativePicardZero
import Langlands.AlgebraicGeometry.Picard.RigidifiedInverse
import Langlands.AlgebraicGeometry.Picard.LineBundleNormalization

/-! # The rigidified Mumford bundle -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- The parameter-first self-product as an object over the original base. -/
abbrev mumfordProduct : Over S :=
  Over.mk (pullback.fst A.X.hom A.X.hom ≫ A.X.hom)

/-- The first projection of the self-product over the base. -/
def mumfordFirst : mumfordProduct A ⟶ A.X :=
  Over.homMk (pullback.fst A.X.hom A.X.hom)

/-- The second projection of the self-product over the base. -/
def mumfordSecond : mumfordProduct A ⟶ A.X :=
  Over.homMk (pullback.snd A.X.hom A.X.hom) pullback.condition.symm

/-- Addition on the actual self-product, using the group law on points. -/
def mumfordAddition : (mumfordProduct A).left ⟶ A.X.left :=
  (mumfordFirst A * mumfordSecond A).left

/-- The section `(id, e)` of the parameter-first family. -/
abbrev mumfordSection : A.X.left ⟶ (mumfordProduct A).left :=
  (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app A.X

/-- The same section as a morphism over the original base. -/
def mumfordSectionOver : A.X ⟶ mumfordProduct A :=
  Over.homMk (mumfordSection A) (by
    change mumfordSection A ≫ (pullback.fst A.X.hom A.X.hom ≫ A.X.hom) = _
    simp [mumfordSection, relativeSection, pullback.lift_fst_assoc])

@[simp] lemma mumfordSectionOver_first :
    mumfordSectionOver A ≫ mumfordFirst A = 𝟙 A.X := by
  apply Over.OverMorphism.ext
  exact relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) A.X

@[simp] lemma mumfordSectionOver_second :
    mumfordSectionOver A ≫ mumfordSecond A = 1 := by
  calc
    mumfordSectionOver A ≫ mumfordSecond A =
        Over.mkIdTerminal.from A.X ≫ (1 : Over.mk (𝟙 S) ⟶ A.X) := by
      apply Over.OverMorphism.ext
      change mumfordSection A ≫ pullback.snd A.X.hom A.X.hom =
        (Over.mkIdTerminal.from A.X).left ≫ (unitSection A)
      rw [Over.mkIdTerminal_from_left]
      exact relativeSection_snd A.X.hom (unitSection A) (unitSection_comp A) A.X
    _ = 1 := by simp

/-- Restricting addition to `(id, e)` is the identity. -/
@[simp] lemma mumfordSection_addition :
    mumfordSection A ≫ mumfordAddition A = 𝟙 A.X.left := by
  change (mumfordSectionOver A ≫ (mumfordFirst A * mumfordSecond A)).left = _
  rw [MonObj.comp_mul, mumfordSectionOver_first, mumfordSectionOver_second, mul_one]
  rfl

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})

/-- Restricting the addition pullback along `(id, e)` recovers the original module. -/
def mumfordAdditionRestrictionIso (L : A.X.left.Modules) :
    (Scheme.Modules.pullback (mumfordSection A)).obj
      ((Scheme.Modules.pullback (mumfordAddition A)).obj L) ≅ L :=
  (Scheme.Modules.pullbackComp (mumfordSection A) (mumfordAddition A)).app L ≪≫
    (Scheme.Modules.pullbackCongr (mumfordSection_addition A)).app L ≪≫
      (Scheme.Modules.pullbackId A.X.left).app L

/-- First rigidify `m*L tensor p1*M` with the supplied evaluation. -/
def mumfordFirstFactor (L : RigidifiedLineBundle (unitSection A))
    (M : LineBundle A.X.left)
    (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left) :
    RigidifiedFamily A A.X :=
  LineBundle.normalize preservation
    (pullback.fst A.X.hom A.X.hom) (mumfordSection A)
    (relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) A.X)
    ((LineBundle.pullback (mumfordAddition A)).obj
      ((RigidifiedLineBundle.forget _).obj L)) M
    ((Langlands.Scheme.Modules.tensorFunctor A.X.left).mapIso
      ((mumfordAdditionRestrictionIso A L.obj.carrier).prod (Iso.refl M.obj)) ≪≫
      evaluation)

/-- The actual rigidified Mumford family, using a specified ordinary inverse
and evaluation, with no Picard-zero conclusion assumed. -/
def mumfordBundle (L : RigidifiedLineBundle (unitSection A))
    (M : LineBundle A.X.left)
    (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left) :
    RigidifiedFamily A A.X :=
  RigidifiedLineBundle.tensor preservation
    (mumfordFirstFactor A preservation L M evaluation)
    ((RigidifiedLineBundle.pullback (pullback.snd A.X.hom A.X.hom) A.X.hom
      (relativeSection_snd A.X.hom (unitSection A) (unitSection_comp A) A.X)).obj
      (RigidifiedLineBundle.rigidifyInverse preservation L M evaluation))

/-- Forgetting rigidification gives exactly the three tensor factors. -/
lemma mumfordBundle_forget (L : RigidifiedLineBundle (unitSection A))
    (M : LineBundle A.X.left)
    (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left) :
    (RigidifiedLineBundle.forget (mumfordSection A)).obj
        (mumfordBundle A preservation L M evaluation) =
      LineBundle.tensor preservation
        (LineBundle.tensor preservation
          ((LineBundle.pullback (mumfordAddition A)).obj
            ((RigidifiedLineBundle.forget _).obj L))
          ((LineBundle.pullback (pullback.fst A.X.hom A.X.hom)).obj M))
        ((LineBundle.pullback (pullback.snd A.X.hom A.X.hom)).obj M) := rfl

end Langlands.AbelianScheme
