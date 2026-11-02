import Langlands.AlgebraicGeometry.PointTopology.RingPointBaseChange

/-!
# Product points in the actual base-changed local models

Restrict a point over a product ring to each factor, then use the actual
pullback-adjunction equivalence to view it as a point of the local model.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (C : Type u) [CommRing C] {ι : Type u} (R : ι → Type u)
variable [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]
variable (X : Over (Spec (CommRingCat.of C)))

/-- Factorwise base change identifies relative points with points of the local models. -/
def localFactorPointEquiv :
    (∀ i, RingPoint C X (R i)) ≃
      ∀ i, RingPoint (R i) (ringBaseChange C (R i) X) (R i) where
  toFun p i := ringPointBaseChangeEquiv C (R i) (R i) X (p i)
  invFun p i := (ringPointBaseChangeEquiv C (R i) (R i) X).symm (p i)
  left_inv p := by
    funext i
    exact (ringPointBaseChangeEquiv C (R i) (R i) X).symm_apply_apply (p i)
  right_inv p := by
    funext i
    exact (ringPointBaseChangeEquiv C (R i) (R i) X).apply_symm_apply (p i)

/-- The actual local-model product map, with the target base changed at each factor. -/
def localProductPointMap :
    RingPoint C X (∀ i, R i) →
      ∀ i, RingPoint (R i) (ringBaseChange C (R i) X) (R i) :=
  fun p => localFactorPointEquiv C R X (productPointMap C R X p)

/-- This map is precisely restriction to each value ring followed by its base change. -/
@[simp]
theorem localProductPointMap_apply (p : RingPoint C X (∀ i, R i)) (i : ι) :
    localProductPointMap C R X p i =
      ringPointBaseChangeEquiv C (R i) (R i) X
        (p.changeRing (Pi.evalAlgHom C R i)) := rfl

/-- Forgetting the local model recovers the existing relative product-point map. -/
@[simp]
theorem localFactorPointEquiv_symm_localProductPointMap
    (p : RingPoint C X (∀ i, R i)) :
    (localFactorPointEquiv C R X).symm (localProductPointMap C R X p) =
      productPointMap C R X p :=
  (localFactorPointEquiv C R X).symm_apply_apply _

/-- The projection to the original scheme is restriction along the coordinate projection. -/
@[simp]
theorem localProductPointMap_left_fst
    (p : RingPoint C X (∀ i, R i)) (i : ι) :
    (localProductPointMap C R X p i).left ≫
      pullback.fst X.hom (Spec.algebraMap C (R i)) =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom R i)) ≫ p.left :=
  ringPointBaseChangeEquiv_left_fst C (R i) (R i) X _

/-- The other projection is the structure map of the local test spectrum. -/
@[simp]
theorem localProductPointMap_left_snd
    (p : RingPoint C X (∀ i, R i)) (i : ι) :
    (localProductPointMap C R X p i).left ≫
      pullback.snd X.hom (Spec.algebraMap C (R i)) =
      Spec.algebraMap (R i) (R i) :=
  ringPointBaseChangeEquiv_left_snd C (R i) (R i) X _

/-- The local-model map commutes with morphisms of the original schemes. -/
theorem localProductPointMap_natural
    {Y : Over (Spec (CommRingCat.of C))} (f : X ⟶ Y)
    (p : RingPoint C X (∀ i, R i)) (i : ι) :
    localProductPointMap C R Y (p ≫ f) i =
      localProductPointMap C R X p i ≫
        (Over.pullback (Spec.algebraMap C (R i))).map f := by
  change ringPointBaseChangeEquiv C (R i) (R i) Y
      (productPointMap C R Y (p ≫ f) i) = _
  rw [productPointMap_natural]
  exact ringPointBaseChangeEquiv_natural C (R i) (R i) f _

end Langlands.AlgebraicGeometry.PointTopology
