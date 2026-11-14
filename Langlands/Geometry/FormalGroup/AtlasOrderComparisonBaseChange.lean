import Langlands.Geometry.FormalGroup.AtlasComparisonBaseChange
import Langlands.Geometry.FormalGroup.AtlasOrderRefinementBaseChange
import Langlands.Geometry.FormalGroup.AtlasOrderComparison

/-! # Coefficient extension of order-linear different-cover comparisons -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {E : OrderAction D X} {E' : OrderAction D Y}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Extend both actual refinements and conjugate the extended order-linear formal isomorphism. -/
def baseChange (f : Comparison E E') (S : CommAlgCat.{v} R) :
    Comparison (E.baseChange S) (E'.baseChange S) where
  left := f.left.baseChange S
  right := f.right.baseChange S
  sameCover := baseOpens_eq S f.sameCover
  coordinateIso := (f.left.orderBaseChangeIso E S).symm.trans
    ((f.coordinateIso.baseChange S).trans (f.right.orderBaseChangeIso E' S))

/-- Forgetting order commutation retains exactly the underlying formal comparison. -/
@[simp]
theorem toBasicComparison_baseChange (f : Comparison E E') (S : CommAlgCat.{v} R) :
    (f.baseChange S).toBasicComparison = f.toBasicComparison.baseChange S := rfl

/-- The full-order formal comparison realizes the coefficient-extension family square. -/
theorem baseChange_onPoints (f : Comparison E E') (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (x : E.Point (restrictTest S A)) :
    (f.baseChange S).onPoints A (E.toBaseChangePoints S A x) =
      E'.toBaseChangePoints S A (f.onPoints (restrictTest S A) x) :=
  f.toBasicComparison.baseChange_onPoints S A x

/-- The inverse full-order comparison gives the reverse complete-family square. -/
theorem baseChange_inv_onPoints (f : Comparison E E') (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (y : E'.Point (restrictTest S A)) :
    ((f.baseChange S).onPoints A).symm (E'.toBaseChangePoints S A y) =
      E.toBaseChangePoints S A ((f.onPoints (restrictTest S A)).symm y) :=
  f.toBasicComparison.baseChange_inv_onPoints S A y

/-- The inverse coefficient-family equivalences give the same order-linear square. -/
theorem baseChange_fromPoints (f : Comparison E E') (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (y : (E.baseChange S).Point A) :
    f.onPoints (restrictTest S A) ((E.baseChangePointEquiv S A).symm y) =
      (E'.baseChangePointEquiv S A).symm ((f.baseChange S).onPoints A y) :=
  f.toBasicComparison.baseChange_fromPoints S A y

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison
