import Langlands.AlgebraicGeometry.Picard.GeometricPicardZeroTensor
import Langlands.AlgebraicGeometry.Picard.RigidifiedInverse
import Langlands.AlgebraicGeometry.Picard.RelativePicardZeroTensor
import Langlands.AlgebraicGeometry.Modules.TensorCoherenceMaps

/-! # A supplied tensor inverse preserves geometric Picard zero -/

universe u

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

namespace Langlands.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- An explicit comparison between two supplied right tensor inverses. -/
def tensorInverseComparisonIso (L M N : X.Modules)
    (eM : tensorObj L M ≅ structureSheaf X)
    (eN : tensorObj L N ≅ structureSheaf X) : M ≅ N :=
  (tensorLeftUnitor M).symm ≪≫
    (tensorFunctor X).mapIso (((tensorComm N L ≪≫ eN).symm).prod (Iso.refl M)) ≪≫
      tensorAssociator N L M ≪≫
        (tensorFunctor X).mapIso ((Iso.refl N).prod eM) ≪≫ tensorRightUnitor N

/-- Pull back a supplied evaluation using the fixed invertible tensor comparison. -/
def pullbackTensorEvaluation (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (f : Y ⟶ X) (L M : X.Modules) (evaluation : tensorObj L M ≅ structureSheaf X) :
    tensorObj ((Scheme.Modules.pullback f).obj L) ((Scheme.Modules.pullback f).obj M) ≅
      structureSheaf Y := by
  letI := preservation f
  exact ((asIso (pullbackTensorComparison f)).app (L, M)).symm ≪≫
    (Scheme.Modules.pullback f).mapIso evaluation ≪≫ pullbackUnitIso f

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard.LineBundle

open Langlands.Scheme.Modules

variable {X : Scheme.{u}}

/-- Comparison of supplied tensor inverses as an actual line-bundle isomorphism. -/
def tensorInverseComparisonIso (L M N : LineBundle X)
    (eM : tensorObj L.obj M.obj ≅ structureSheaf X)
    (eN : tensorObj L.obj N.obj ≅ structureSheaf X) : M ≅ N :=
  ObjectProperty.isoMk _ (Langlands.Scheme.Modules.tensorInverseComparisonIso
    L.obj M.obj N.obj eM eN)

end Langlands.AlgebraicGeometry.Picard.LineBundle

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable {S : Scheme.{u}} (G : GroupScheme S)

include preservation in
/-- A supplied tensor inverse of a translation-invariant line bundle is translation invariant. -/
lemma isTranslationInvariant_tensorInverse {L M : LineBundle G.X.left}
    (evaluation : tensorObj L.obj M.obj ≅ structureSheaf G.X.left)
    (hL : IsTranslationInvariant G L) : IsTranslationInvariant G M := by
  intro x
  obtain ⟨d⟩ := hL x
  let f := (translation G x).left
  let e : tensorObj L.obj ((LineBundle.pullback f).obj M).obj ≅ structureSheaf G.X.left :=
    (tensorFunctor G.X.left).mapIso
      (((LineBundle.forget G.X.left).mapIso d.symm).prod (Iso.refl _)) ≪≫
        pullbackTensorEvaluation preservation f L.obj M.obj evaluation
  exact ⟨LineBundle.tensorInverseComparisonIso L ((LineBundle.pullback f).obj M) M e evaluation⟩

end Langlands.GroupScheme

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S)

include preservation in
/-- A supplied tensor inverse of a geometrically Picard-zero bundle is geometrically Picard zero. -/
lemma isGeometricallyPicardZero_tensorInverse {L M : LineBundle A.X.left}
    (evaluation : tensorObj L.obj M.obj ≅ structureSheaf A.X.left)
    (hL : IsGeometricallyPicardZero A L) : IsGeometricallyPicardZero A M := by
  intro K _ _ s
  exact GroupScheme.isTranslationInvariant_tensorInverse preservation ((baseChange s).obj A).toGrp
    (L := fibreLineBundle A L s) (M := fibreLineBundle A M s)
    (pullbackTensorEvaluation preservation (pullback.fst A.X.hom s) L.obj M.obj evaluation)
    (hL K s)

include preservation in
/-- The constructed rigidification of a supplied ordinary inverse preserves the
geometric Picard-zero condition on relative families. -/
lemma isPicardZeroFamily_rigidifyInverse {T : Over S} (L : RigidifiedFamily A T)
    (M : LineBundle ((relativeSpace A.X.hom).obj T))
    (evaluation : tensorObj L.obj.carrier M.obj ≅
      structureSheaf ((relativeSpace A.X.hom).obj T))
    (hL : IsPicardZeroFamily A L) :
    IsPicardZeroFamily A (RigidifiedLineBundle.rigidifyInverse preservation L M evaluation) := by
  exact isGeometricallyPicardZero_tensorInverse preservation ((baseChange T.hom).obj A)
    (L := familyLineBundle A L)
    (M := familyLineBundle A (RigidifiedLineBundle.rigidifyInverse preservation L M evaluation))
    (pullbackTensorEvaluation preservation (relativeSpaceSymmetry A.X.hom T).inv
      L.obj.carrier M.obj evaluation) hL

/-- The geometric Picard-zero class of the rigidified supplied inverse. -/
def picardZeroInverseClass {T : Over S} (L : RigidifiedFamily A T)
    (M : LineBundle ((relativeSpace A.X.hom).obj T))
    (evaluation : tensorObj L.obj.carrier M.obj ≅
      structureSheaf ((relativeSpace A.X.hom).obj T))
    (hL : IsPicardZeroFamily A L) : PicardZeroClasses A T :=
  ⟨RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
      (RigidifiedLineBundle.rigidifyInverse preservation L M evaluation),
    isPicardZeroFamily_rigidifyInverse preservation A L M evaluation hL⟩

/-- The supplied inverse class satisfies the actual tensor inverse equation
inside the geometric Picard-zero subset. -/
lemma picardZeroClassesTensor_inverseClass {T : Over S} (L : RigidifiedFamily A T)
    (M : LineBundle ((relativeSpace A.X.hom).obj T))
    (evaluation : tensorObj L.obj.carrier M.obj ≅
      structureSheaf ((relativeSpace A.X.hom).obj T))
    (hL : IsPicardZeroFamily A L) :
    picardZeroClassesTensor preservation A T
        ⟨RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) L, hL⟩
        (picardZeroInverseClass preservation A L M evaluation hL) =
      trivialPicardZeroClass A T := by
  apply Subtype.ext
  exact RigidifiedLineBundle.classesTensor_rigidifyInverse preservation
    A.X.hom (unitSection A) (unitSection_comp A) L M evaluation

end Langlands.AbelianScheme
