import Langlands.Geometry.FormalGroup.AtlasRefinementSource

/-! # Equivalence laws for formal atlas comparisons after refinement -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace Comparison

variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}

/-- The induced map is characterized by restriction to its right refinement. -/
theorem onPoints_restrict (f : Comparison X Y) (A : CommAlgCat.{v} R) (x : X.Point A) :
    f.right.onPoints A (f.onPoints A x) =
      f.coordinateIso.hom.onPoints A (f.left.onPoints A x) :=
  (f.right.pointEquiv A).apply_symm_apply _

/-- Any atlas compares with itself through its actual reflexive refinement. -/
def refl (X : BasicAtlas O R σ) : Comparison X X where
  left := CoverRefinement.refl X
  right := CoverRefinement.refl X
  sameCover := rfl
  coordinateIso := Iso.refl _

/-- Reverse the actual refined formal isomorphism. -/
def symm (f : Comparison X Y) : Comparison Y X where
  left := f.right
  right := f.left
  sameCover := f.sameCover.symm
  coordinateIso := f.coordinateIso.symm

/-- Pull a comparison to a further actual refinement and compose the containments. -/
def refine (f : Comparison X Y) (q : CoverRefinement f.left.atlas) : Comparison X Y where
  left := f.left.comp q
  right := f.right.comp (q.retarget f.right.atlas f.sameCover)
  sameCover := rfl
  coordinateIso := (f.left.compIso q).trans
    ((f.coordinateIso.restrict q).trans
      (f.right.compIso (q.retarget f.right.atlas f.sameCover)).symm)

/-- Join comparisons whose middle refinements have equal finer covers. -/
def join (f : Comparison X Y) (g : Comparison Y Z)
    (h : f.right.opens = g.left.opens) : Comparison X Z where
  left := f.left
  right := g.right
  sameCover := f.sameCover.trans (h.trans g.sameCover)
  coordinateIso := f.coordinateIso.trans
    ((f.right.sourceIso g.left h).trans g.coordinateIso)

/-- Refine both witnesses to an actual product cover before composing their formal maps. -/
def trans (f : Comparison X Y) (g : Comparison Y Z) : Comparison X Z :=
  (f.refine (commonLeft f.left.atlas g.left.atlas)).join
    (g.refine (commonRight f.left.atlas g.left.atlas)) rfl

/-- The reflexive comparison fixes every full point family. -/
@[simp]
theorem onPoints_refl (X : BasicAtlas O R σ) (A : CommAlgCat.{v} R) (x : X.Point A) :
    (refl X).onPoints A x = x := by
  apply ((refl X).right.pointEquiv A).injective
  exact ((refl X).onPoints_restrict A x).trans (Hom.onPoints_id _ _ _)

/-- Reversing the formal comparison reverses the actual point equivalence. -/
@[simp]
theorem onPoints_symm (f : Comparison X Y) (A : CommAlgCat.{v} R) :
    f.symm.onPoints A = (f.onPoints A).symm := rfl

/-- Further refinement leaves the induced map on original full families unchanged. -/
theorem onPoints_refine (f : Comparison X Y) (q : CoverRefinement f.left.atlas)
    (A : CommAlgCat.{v} R) (x : X.Point A) :
    (f.refine q).onPoints A x = f.onPoints A x := by
  let qr := q.retarget f.right.atlas f.sameCover
  apply ((f.refine q).right.pointEquiv A).injective
  refine ((f.refine q).onPoints_restrict A x).trans ?_
  change (((f.right.compIso qr).inv.comp (f.coordinateIso.restrict q).hom).comp
      (f.left.compIso q).hom).onPoints A ((f.left.comp q).onPoints A x) =
    (f.right.comp qr).onPoints A (f.onPoints A x)
  refine (Hom.onPoints_comp _ _ A _).trans ?_
  refine (Hom.onPoints_comp _ _ A _).trans ?_
  change ((f.right.compIso qr).onPoints A).symm
      ((f.coordinateIso.restrict q).hom.onPoints A
        ((f.left.compIso q).hom.onPoints A ((f.left.comp q).onPoints A x))) =
    (f.right.comp qr).onPoints A (f.onPoints A x)
  apply ((f.right.compIso qr).onPoints A).symm_apply_eq.mpr
  exact (congrArg ((f.coordinateIso.restrict q).hom.onPoints A)
    (f.left.comp_onPoints q A x)).trans
      ((f.coordinateIso.hom.restrict_onPoints q A (f.left.onPoints A x)).trans
        ((congrArg (qr.onPoints A) (f.onPoints_restrict A x).symm).trans
          (f.right.comp_onPoints qr A (f.onPoints A x)).symm))

/-- Joining compatible finer covers composes their induced point equivalences. -/
theorem onPoints_join (f : Comparison X Y) (g : Comparison Y Z)
    (h : f.right.opens = g.left.opens) (A : CommAlgCat.{v} R) (x : X.Point A) :
    (f.join g h).onPoints A x = g.onPoints A (f.onPoints A x) := by
  apply (g.right.pointEquiv A).injective
  refine ((f.join g h).onPoints_restrict A x).trans ?_
  change ((g.coordinateIso.hom.comp (f.right.sourceIso g.left h).hom).comp
      f.coordinateIso.hom).onPoints A (f.left.onPoints A x) =
    g.right.onPoints A (g.onPoints A (f.onPoints A x))
  refine (Hom.onPoints_comp _ _ A _).trans ?_
  refine (Hom.onPoints_comp _ _ A _).trans ?_
  exact (congrArg (g.coordinateIso.hom.onPoints A)
    ((congrArg ((f.right.sourceIso g.left h).hom.onPoints A)
      (f.onPoints_restrict A x).symm).trans
        (f.right.source_onPoints g.left h A (f.onPoints A x)))).trans
    (g.onPoints_restrict A (f.onPoints A x)).symm

/-- The formal product-cover composite realizes composition on every full point module. -/
@[simp]
theorem onPoints_trans (f : Comparison X Y) (g : Comparison Y Z)
    (A : CommAlgCat.{v} R) (x : X.Point A) :
    (f.trans g).onPoints A x = g.onPoints A (f.onPoints A x) :=
  ((f.refine (commonLeft f.left.atlas g.left.atlas)).onPoints_join
    (g.refine (commonRight f.left.atlas g.left.atlas)) rfl A x).trans
      ((congrArg ((g.refine (commonRight f.left.atlas g.left.atlas)).onPoints A)
        (f.onPoints_refine (commonLeft f.left.atlas g.left.atlas) A x)).trans
          (g.onPoints_refine (commonRight f.left.atlas g.left.atlas) A
            (f.onPoints A x)))

end Comparison

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
