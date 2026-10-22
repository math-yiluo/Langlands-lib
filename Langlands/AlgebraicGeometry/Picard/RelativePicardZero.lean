import Langlands.AlgebraicGeometry.Picard.GeometricPicardZero
import Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalBundle

/-! # Geometric Picard-zero classes in the rigidified relative family -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- The identity point of the group-valued functor of points is the unit section. -/
def unitSection : S ⟶ A.X.left :=
  (1 : Over.mk (𝟙 S) ⟶ A.X).left

@[simp] lemma unitSection_comp : unitSection A ≫ A.X.hom = 𝟙 S :=
  (1 : Over.mk (𝟙 S) ⟶ A.X).w

/-- The existing relative family rigidified along the unit section. -/
abbrev RigidifiedFamily (T : Over S) :=
  RigidifiedLineBundle.relative A.X.hom (unitSection A) (unitSection_comp A) T

/-- Isomorphism classes in the existing rigidified relative family. -/
abbrev RigidifiedClasses (T : Over S) :=
  RigidifiedLineBundle.Classes A.X.hom (unitSection A) (unitSection_comp A) T

/-- Move the underlying bundle from `T ×_S A` to the chosen total space `A ×_S T`. -/
def familyLineBundle {T : Over S} (L : RigidifiedFamily A T) :
    LineBundle ((baseChange T.hom).obj A).X.left :=
  (LineBundle.pullback (relativeSpaceSymmetry A.X.hom T).inv).obj
    ((RigidifiedLineBundle.forget _).obj L)

/-- The geometric-fibre condition on an actual rigidified relative line bundle. -/
def IsPicardZeroFamily {T : Over S} (L : RigidifiedFamily A T) : Prop :=
  IsGeometricallyPicardZero ((baseChange T.hom).obj A) (familyLineBundle A L)

/-- The geometric-fibre condition depends only on the rigidified isomorphism class. -/
lemma isPicardZeroFamily_iff_of_iso {T : Over S} {L M : RigidifiedFamily A T}
    (e : L ≅ M) : IsPicardZeroFamily A L ↔ IsPicardZeroFamily A M :=
  isGeometricallyPicardZero_iff_of_iso _
    ((LineBundle.pullback (relativeSpaceSymmetry A.X.hom T).inv).mapIso
      ((RigidifiedLineBundle.forget _).mapIso e))

/-- Descend the geometric-fibre predicate to isomorphism classes. -/
def IsPicardZeroClass {T : Over S} (q : RigidifiedClasses A T) : Prop :=
  Quotient.lift (s := isIsomorphicSetoid (RigidifiedFamily A T)) (IsPicardZeroFamily A)
    (fun _ _ ⟨e⟩ ↦ propext (isPicardZeroFamily_iff_of_iso A e)) q

/-- The class predicate agrees with the condition on any representative. -/
@[simp] lemma isPicardZeroClass_classOf {T : Over S} (L : RigidifiedFamily A T) :
    IsPicardZeroClass A
      (RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) L) ↔
        IsPicardZeroFamily A L :=
  Iff.rfl

/-- The subset of rigidified classes satisfying the geometric-fibre condition. -/
abbrev PicardZeroClasses (T : Over S) :=
  {q : RigidifiedClasses A T // IsPicardZeroClass A q}

/-- The structure line bundle with its canonical rigidification satisfies the condition. -/
lemma isPicardZeroFamily_trivial (T : Over S) :
    IsPicardZeroFamily A
      (RigidifiedLineBundle.trivial
        ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T)) := by
  apply isGeometricallyPicardZero_of_iso _
    (LineBundle.pullbackTrivialIso (relativeSpaceSymmetry A.X.hom T).inv).symm
  exact isGeometricallyPicardZero_trivial _

/-- The class of the canonically rigidified structure line bundle lies in the subset. -/
def trivialPicardZeroClass (T : Over S) : PicardZeroClasses A T :=
  ⟨RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
      (RigidifiedLineBundle.trivial
        ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T)),
    isPicardZeroFamily_trivial A T⟩

end Langlands.AbelianScheme
