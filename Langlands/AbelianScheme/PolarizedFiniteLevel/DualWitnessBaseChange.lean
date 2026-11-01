import Langlands.AlgebraicGeometry.Picard.PoincareSliceSymmetryBaseChange
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZeroInverse
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeGeometryStatement

/-! # Transporting supplied dual witnesses along arbitrary base change -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (universality : PicardZeroUniversalBaseChangeStatement.{u})
variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)
variable (hA : HasDualScheme A)

include universality in
/-- The geometry of the original dual transports to any chosen changed dual
through the actual canonical comparison. -/
theorem dualSchemeGeometry_baseChange (geometryA : DualSchemeGeometry A hA)
    (hA' : HasDualScheme ((AbelianScheme.baseChange b).obj A)) :
    DualSchemeGeometry ((AbelianScheme.baseChange b).obj A) hA' := by
  let D := dualScheme A hA
  let D' := (Over.pullback b).obj D
  let e := dualSchemeBaseChangeIso universality b A hA hA'
  let : Smooth D.hom := geometryA.1
  let : IsProper D.hom := geometryA.2.1
  let : GeometricallyConnected D.hom := geometryA.2.2
  let : Smooth D'.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd D.hom b)
    infer_instance
  let : IsProper D'.hom := by
    change IsProper (CategoryTheory.Limits.pullback.snd D.hom b)
    infer_instance
  let : GeometricallyConnected D'.hom := by
    change GeometricallyConnected (CategoryTheory.Limits.pullback.snd D.hom b)
    infer_instance
  let : IsIso e.inv.left := ((Over.forget S').mapIso e).isIso_inv
  have he : e.inv.left ≫ D'.hom = (dualScheme ((AbelianScheme.baseChange b).obj A) hA').hom :=
    e.inv.w
  have hgc : GeometricallyConnected
      (dualScheme ((AbelianScheme.baseChange b).obj A) hA').hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso
        (fst := e.inv.left) (g := 𝟙 S') ⟨by simpa using he⟩)
      (inferInstance : GeometricallyConnected D'.hom)
  exact ⟨he ▸ (inferInstance : Smooth (e.inv.left ≫ D'.hom)),
    he ▸ (inferInstance : IsProper (e.inv.left ≫ D'.hom)), hgc⟩

/-- The actual total-space map identifying the changed Poincare bundle with a
pullback of the original one. -/
def dualWitnessBaseChangeSpaceMap :
    (relativeSpace ((AbelianScheme.baseChange b).obj A).X.hom).obj
        (dualScheme ((AbelianScheme.baseChange b).obj A)
          (hasDualScheme_baseChange universality b A hA)) ⟶
      (relativeSpace A.X.hom).obj (dualScheme A hA) :=
  (relativeSpace ((AbelianScheme.baseChange b).obj A).X.hom).map
      (dualSchemeBaseChangeIso universality b A hA
        (hasDualScheme_baseChange universality b A hA)).inv ≫
    baseChangeFamilySpaceMap b A (dualScheme A hA)

variable (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))

/-- Pull back the supplied original inverse; no inverse-existence premise is
needed at the changed base. -/
def dualWitnessBaseChangeInverseBundle :
    LineBundle ((relativeSpace ((AbelianScheme.baseChange b).obj A).X.hom).obj
      (dualScheme ((AbelianScheme.baseChange b).obj A)
        (hasDualScheme_baseChange universality b A hA))) :=
  (LineBundle.pullback (dualWitnessBaseChangeSpaceMap universality b A hA)).obj MA

/-- Pulling back the original evaluation and using the canonical Poincare
comparison gives an evaluation on the changed dual. -/
def dualWitnessBaseChangeEvaluation
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
      structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA))) :
    tensorObj
        (poincareFamily ((AbelianScheme.baseChange b).obj A)
          (hasDualScheme_baseChange universality b A hA)).obj.carrier
        (dualWitnessBaseChangeInverseBundle universality b A hA MA).obj ≅
      structureSheaf ((relativeSpace ((AbelianScheme.baseChange b).obj A).X.hom).obj
        (dualScheme ((AbelianScheme.baseChange b).obj A)
          (hasDualScheme_baseChange universality b A hA))) :=
  (tensorFunctor _).mapIso
      (((LineBundle.forget _).mapIso
        (poincareBaseChangeForgetPullbackIso universality b A hA)).prod (Iso.refl _)) ≪≫
    pullbackTensorEvaluation preservation
      (dualWitnessBaseChangeSpaceMap universality b A hA)
      (poincareFamily A hA).obj.carrier MA.obj evaluationA

end Langlands.AbelianScheme.PolarizedFiniteLevel
