import Langlands.Geometry.FormalGroup.AtlasOrderComparison
import Langlands.Geometry.FormalGroup.AtlasOrderRefinementCoherence
import Langlands.Geometry.FormalGroup.AtlasComparisonEquivalence

/-! # Equivalence operations on actual order-linear atlas comparisons -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {E : OrderAction D X} {E' : OrderAction D Y} {E'' : OrderAction D Z}

/-- The reflexive comparison uses the actual reflexive refinement and its order action. -/
def refl (E : OrderAction D X) : Comparison E E where
  left := CoverRefinement.refl X
  right := CoverRefinement.refl X
  sameCover := rfl
  coordinateIso := Iso.refl _

/-- Reverse the actual refined order-linear formal maps. -/
def symm (f : Comparison E E') : Comparison E' E where
  left := f.right
  right := f.left
  sameCover := f.sameCover.symm
  coordinateIso := f.coordinateIso.symm

/-- Restrict both formal maps and compare direct with successive order restriction. -/
def refine (f : Comparison E E') (q : CoverRefinement f.left.atlas) : Comparison E E' where
  left := f.left.comp q
  right := f.right.comp (q.retarget f.right.atlas f.sameCover)
  sameCover := rfl
  coordinateIso := (f.left.orderCompIso E q).trans
    ((f.coordinateIso.restrict q).trans
      (f.right.orderCompIso E' (q.retarget f.right.atlas f.sameCover)).symm)

/-- Compose on equal middle covers via their actual order-compatible source transitions. -/
def join (f : Comparison E E') (g : Comparison E' E'')
    (h : f.right.opens = g.left.opens) : Comparison E E'' where
  left := f.left
  right := g.right
  sameCover := f.sameCover.trans (h.trans g.sameCover)
  coordinateIso := f.coordinateIso.trans
    ((f.right.orderSourceIso E' g.left h).trans g.coordinateIso)

/-- Refine to a genuine product cover and compose actual order-linear formal comparisons. -/
def trans (f : Comparison E E') (g : Comparison E' E'') : Comparison E E'' :=
  (f.refine (commonLeft f.left.atlas g.left.atlas)).join
    (g.refine (commonRight f.left.atlas g.left.atlas)) rfl

/-- Forgetting order commutation retains the existing reflexive formal comparison. -/
theorem toBasicComparison_refl (E : OrderAction D X) :
    (refl E).toBasicComparison = BasicAtlas.Comparison.refl X := rfl

/-- Reversal retains exactly the existing underlying formal inverse comparison. -/
theorem toBasicComparison_symm (f : Comparison E E') :
    f.symm.toBasicComparison = f.toBasicComparison.symm := rfl

/-- The new refinement uses the existing actual underlying restricted formal maps. -/
theorem toBasicComparison_refine (f : Comparison E E') (q : CoverRefinement f.left.atlas) :
    (f.refine q).toBasicComparison = f.toBasicComparison.refine q := rfl

/-- Joining retains the same underlying actual source-chart transition. -/
theorem toBasicComparison_join (f : Comparison E E') (g : Comparison E' E'')
    (h : f.right.opens = g.left.opens) :
    (f.join g h).toBasicComparison = f.toBasicComparison.join g.toBasicComparison h := rfl

/-- The product-cover composite has the same underlying actual formal maps. -/
theorem toBasicComparison_trans (f : Comparison E E') (g : Comparison E' E'') :
    (f.trans g).toBasicComparison = f.toBasicComparison.trans g.toBasicComparison := rfl

/-- The reflexive order-linear comparison fixes each complete family. -/
@[simp]
theorem onPoints_refl (E : OrderAction D X) (A : CommAlgCat.{v} R) (x : E.Point A) :
    (refl E).onPoints A x = x :=
  BasicAtlas.Comparison.onPoints_refl X A x

/-- Reversing the actual formal maps reverses the order-linear family equivalence. -/
@[simp]
theorem onPoints_symm (f : Comparison E E') (A : CommAlgCat.{v} R) :
    f.symm.onPoints A = (f.onPoints A).symm := rfl

/-- Further actual refinement leaves the original full-family map unchanged. -/
theorem onPoints_refine (f : Comparison E E') (q : CoverRefinement f.left.atlas)
    (A : CommAlgCat.{v} R) (x : E.Point A) :
    (f.refine q).onPoints A x = f.onPoints A x :=
  BasicAtlas.Comparison.onPoints_refine f.toBasicComparison q A x

/-- The join realizes composition on every full order-module family. -/
theorem onPoints_join (f : Comparison E E') (g : Comparison E' E'')
    (h : f.right.opens = g.left.opens) (A : CommAlgCat.{v} R) (x : E.Point A) :
    (f.join g h).onPoints A x = g.onPoints A (f.onPoints A x) :=
  BasicAtlas.Comparison.onPoints_join f.toBasicComparison g.toBasicComparison h A x

/-- The actual product-cover composite realizes composition of the D-linear equivalences. -/
@[simp]
theorem onPoints_trans (f : Comparison E E') (g : Comparison E' E'')
    (A : CommAlgCat.{v} R) (x : E.Point A) :
    (f.trans g).onPoints A x = g.onPoints A (f.onPoints A x) :=
  BasicAtlas.Comparison.onPoints_trans f.toBasicComparison g.toBasicComparison A x

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison
