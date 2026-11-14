import Langlands.Geometry.FormalGroup.AtlasOrderRefinement
import Langlands.Geometry.FormalGroup.AtlasComparison

/-! # Actual order-linear comparisons of formal atlases on different covers -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}

/-- A comparison supplies actual order-linear formal maps on a common refinement. -/
structure Comparison (E : OrderAction D X) (E' : OrderAction D Y) where
  left : CoverRefinement X
  right : CoverRefinement Y
  sameCover : left.opens = right.opens
  coordinateIso : Iso (left.orderAction E) (right.orderAction E') sameCover

namespace Comparison

variable {E : OrderAction D X} {E' : OrderAction D Y}

/-- Forget order commutation while retaining the same actual formal maps and refinements. -/
def toBasicComparison (f : Comparison E E') : BasicAtlas.Comparison X Y where
  left := f.left
  right := f.right
  sameCover := f.sameCover
  coordinateIso := {
    hom := f.coordinateIso.hom.val
    inv := f.coordinateIso.inv.val
    inv_hom := congrArg Subtype.val f.coordinateIso.inv_hom
    hom_inv := congrArg Subtype.val f.coordinateIso.hom_inv }

/-- Restrict, evaluate the actual formal isomorphism, then glue the full right family. -/
def onPoints (f : Comparison E E') (A : CommAlgCat.{v} R) :
    E.Point A ≃ₗ[D] E'.Point A :=
  ((f.left.orderPointEquiv E A).trans (f.coordinateIso.onPoints A)).trans
    (f.right.orderPointEquiv E' A).symm

/-- Forgetting the scalar structure gives the same actual function on complete families. -/
theorem onPoints_toBasicComparison (f : Comparison E E') (A : CommAlgCat.{v} R)
    (x : E.Point A) :
    f.onPoints A x = f.toBasicComparison.onPoints A x := rfl

/-- Restriction to the right finer cover characterizes the constructed family map. -/
theorem onPoints_restrict (f : Comparison E E') (A : CommAlgCat.{v} R)
    (x : E.Point A) :
    f.right.orderOnPoints E' A (f.onPoints A x) =
      f.coordinateIso.hom.onPoints A (f.left.orderOnPoints E A x) :=
  (f.right.orderPointEquiv E' A).apply_symm_apply _

/-- The formal comparison induces a natural isomorphism of actual order-module functors. -/
def pointFunctorIso (f : Comparison E E') : E.pointFunctor ≅ E'.pointFunctor :=
  ((f.left.orderPointFunctorIso E).trans f.coordinateIso.pointNatIso).trans
    (f.right.orderPointFunctorIso E').symm

/-- The component of the constructed natural isomorphism is the same full-family map. -/
@[simp]
theorem pointFunctorIso_hom_app (f : Comparison E E') (A : CommAlgCat.{v} R)
    (x : E.Point A) :
    (f.pointFunctorIso.hom.app A) x = f.onPoints A x := rfl

/-- The different-cover family map commutes with every coefficient-algebra map. -/
theorem onPoints_natural (f : Comparison E E') {A B : CommAlgCat.{v} R}
    (φ : A ⟶ B) (x : E.Point A) :
    E'.mapPoints φ (f.onPoints A x) = f.onPoints B (E.mapPoints φ x) :=
  (congrArg (fun g => g x) (f.pointFunctorIso.hom.naturality φ)).symm

/-- Restrict the same formal comparison to actual coefficient algebras with nilpotent pi. -/
def nilpPointFunctorIso (f : Comparison E E') (π : R) :
    E.nilpPointFunctor π ≅ E'.nilpPointFunctor π :=
  Functor.isoWhiskerLeft (Nilp.forget R π) f.pointFunctorIso

/-- The product principal cover supplies both refinements; the input is a formal isomorphism. -/
def ofCommon (f : Iso ((commonLeft X Y).orderAction E)
    ((commonRight X Y).orderAction E') rfl) : Comparison E E' where
  left := commonLeft X Y
  right := commonRight X Y
  sameCover := rfl
  coordinateIso := f

end Comparison

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
