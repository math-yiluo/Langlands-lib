import Langlands.Geometry.FormalGroup.AtlasRefinementBaseChange
import Langlands.Geometry.FormalGroup.AtlasComparisonEquivalence

/-! # Coefficient extension of comparisons on different principal covers -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.Comparison

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Extend the two refinements and conjugate the extended formal coordinate isomorphism. -/
def baseChange (f : Comparison X Y) (S : CommAlgCat.{v} R) :
    Comparison (X.baseChange S) (Y.baseChange S) where
  left := f.left.baseChange S
  right := f.right.baseChange S
  sameCover := baseOpens_eq S f.sameCover
  coordinateIso := (f.left.baseChangeIso S).symm.trans
    ((f.coordinateIso.baseChange S).trans (f.right.baseChangeIso S))

/-- The extended different-cover formal comparison gives the full-family square. -/
theorem baseChange_onPoints (f : Comparison X Y) (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (x : X.Point (restrictTest S A)) :
    (f.baseChange S).onPoints A (X.toBaseChangePoints S A x) =
      Y.toBaseChangePoints S A (f.onPoints (restrictTest S A) x) := by
  apply ((f.right.baseChange S).pointEquiv A).injective
  refine ((f.baseChange S).onPoints_restrict A _).trans ?_
  change (((f.right.baseChangeIso S).hom.comp (f.coordinateIso.baseChange S).hom).comp
    (f.left.baseChangeIso S).inv).onPoints A
      ((f.left.baseChange S).onPoints A (X.toBaseChangePoints S A x)) =
        (f.right.baseChange S).onPoints A
          (Y.toBaseChangePoints S A (f.onPoints (restrictTest S A) x))
  refine (Hom.onPoints_comp _ _ A _).trans ?_
  refine (Hom.onPoints_comp _ _ A _).trans ?_
  change (f.right.baseChangeIso S).onPoints A
    ((f.coordinateIso.baseChange S).onPoints A
      (((f.left.baseChangeIso S).onPoints A).symm
        ((f.left.baseChange S).onPoints A (X.toBaseChangePoints S A x)))) = _
  refine (congrArg (fun z => (f.right.baseChangeIso S).onPoints A
    ((f.coordinateIso.baseChange S).onPoints A z))
      (f.left.baseChange_inv_onPoints S A x)).trans ?_
  refine (congrArg ((f.right.baseChangeIso S).onPoints A)
    (f.coordinateIso.baseChange_onPoints S A (f.left.onPoints (restrictTest S A) x))).trans ?_
  exact (congrArg (fun z => (f.right.baseChangeIso S).onPoints A
    (f.right.atlas.toBaseChangePoints S A z))
      (f.onPoints_restrict (restrictTest S A) x).symm).trans
        (f.right.baseChange_onPoints S A _)

/-- The inverse different-cover comparison gives the reverse full-family square. -/
theorem baseChange_inv_onPoints (f : Comparison X Y) (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (y : Y.Point (restrictTest S A)) :
    ((f.baseChange S).onPoints A).symm (Y.toBaseChangePoints S A y) =
      X.toBaseChangePoints S A ((f.onPoints (restrictTest S A)).symm y) := by
  apply ((f.baseChange S).onPoints A).symm_apply_eq.mpr
  exact ((f.baseChange_onPoints S A ((f.onPoints (restrictTest S A)).symm y)).trans
    (congrArg (Y.toBaseChangePoints S A)
      ((f.onPoints (restrictTest S A)).apply_symm_apply y))).symm

/-- Inverse coefficient-family comparisons give the reverse square on every family. -/
theorem baseChange_fromPoints (f : Comparison X Y) (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (y : (X.baseChange S).Point A) :
    f.onPoints (restrictTest S A) ((X.baseChangePointEquiv S A).symm y) =
      (Y.baseChangePointEquiv S A).symm ((f.baseChange S).onPoints A y) := by
  apply (Y.baseChangePointEquiv S A).injective
  change Y.toBaseChangePoints S A
    (f.onPoints (restrictTest S A) ((X.baseChangePointEquiv S A).symm y)) =
      Y.baseChangePointEquiv S A
        ((Y.baseChangePointEquiv S A).symm ((f.baseChange S).onPoints A y))
  rw [← f.baseChange_onPoints]
  exact (congrArg ((f.baseChange S).onPoints A)
    ((X.baseChangePointEquiv S A).apply_symm_apply y)).trans
      ((Y.baseChangePointEquiv S A).apply_symm_apply _).symm

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.Comparison
