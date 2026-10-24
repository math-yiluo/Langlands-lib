import Langlands.AlgebraicGeometry.Picard.DualSchemeBaseChange
import Langlands.AlgebraicGeometry.Picard.MumfordLineBundle
import Langlands.AlgebraicGeometry.Picard.Ample

/-! # Ample Mumford presentations under actual dual base change -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (square : MumfordBundlePicardZeroStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S) (hA : HasDualScheme A)

/-- A scheme map is the classifier of the normalized family of some ample line bundle.
The inverse and evaluation choices are quantified explicitly. -/
def HasAmpleMumfordPresentation (f : A.X ⟶ dualScheme A hA) : Prop :=
  ∃ (L : LineBundle A.X.left) (B : LineBundle S)
    (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅
      structureSheaf S)
    (M : LineBundle A.X.left)
    (evaluation : tensorObj
      (LineBundle.normalize preservation A.X.hom (unitSection A) (unitSection_comp A)
        L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left),
    L.IsAmple ∧ f = mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation
      square hA

/-- The equality in the presentation is equivalent to the actual rigidified pullback
condition, for each fixed set of line-bundle and evaluation choices. -/
lemma eq_mumfordSchemeMapOfLineBundle_iff (f : A.X ⟶ dualScheme A hA)
    (L : LineBundle A.X.left) (B : LineBundle S)
    (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅
      structureSheaf S)
    (M : LineBundle A.X.left)
    (evaluation : tensorObj
      (LineBundle.normalize preservation A.X.hom (unitSection A) (unitSection_comp A)
        L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left) :
    f = mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA ↔
      Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) f).obj (poincareFamily A hA) ≅
          mumfordFamilyOfLineBundle preservation A L B evaluationB M evaluation) := by
  constructor
  · rintro rfl
    exact ⟨mumfordSchemeMapOfLineBundlePullbackIso preservation A L B evaluationB M
      evaluation square hA⟩
  · rintro ⟨e⟩
    exact mumfordSchemeMapOfLineBundle_unique preservation A L B evaluationB M evaluation
      square hA f e

variable (universality : PicardZeroUniversalBaseChangeStatement.{u})
variable {S' : Scheme.{u}} (b : S' ⟶ S)

/-- Pull back a given map and then use the unique Poincare-compatible comparison
with the dual of the changed abelian scheme. -/
def dualBaseChangeMap (f : A.X ⟶ dualScheme A hA) :
    ((baseChange b).obj A).X ⟶
      dualScheme ((baseChange b).obj A) (hasDualScheme_baseChange universality b A hA) :=
  (Over.pullback b).map f ≫
    (dualSchemeBaseChangeIso universality b A hA
      (hasDualScheme_baseChange universality b A hA)).hom

/-- The changed map uses the actual scheme pullback and the canonical dual comparison. -/
lemma dualBaseChangeMap_eq (f : A.X ⟶ dualScheme A hA) :
    dualBaseChangeMap A hA universality b f =
      (Over.pullback b).map f ≫
        (dualSchemeBaseChangeIso universality b A hA
          (hasDualScheme_baseChange universality b A hA)).hom := rfl

/-- The ample Mumford condition after a specified change of base. -/
def HasAmpleMumfordAfterBaseChange (f : A.X ⟶ dualScheme A hA) : Prop :=
  HasAmpleMumfordPresentation preservation square ((baseChange b).obj A)
    (hasDualScheme_baseChange universality b A hA)
    (dualBaseChangeMap A hA universality b f)

end Langlands.AbelianScheme
