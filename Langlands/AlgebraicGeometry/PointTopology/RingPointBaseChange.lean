import Langlands.AlgebraicGeometry.PointTopology.ProductRingPoints
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.Algebra.Algebra.Tower

/-!
# Base change of actual relative scheme points

The pullback adjunction identifies points of a scheme over `Spec C` with
points of its actual base change to `Spec D`, for a compatible `D`-algebra.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (C D : Type u) [CommRing C] [CommRing D] [Algebra C D]

/-- The actual base change of a scheme along `Spec D ⟶ Spec C`. -/
def ringBaseChange (X : Over (Spec (CommRingCat.of C))) :
    Over (Spec (CommRingCat.of D)) :=
  (Over.pullback (Spec.algebraMap C D)).obj X

variable (A : Type u) [CommRing A] [Algebra C A] [Algebra D A]
variable [IsScalarTower C D A]

/-- Restriction of scalars leaves the test spectrum unchanged. -/
def ringTestRestrictScalarsIso :
    (Over.map (Spec.algebraMap C D)).obj (ringTest D A) ≅ ringTest C A :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Spec.algebraMap C A =
      Spec.algebraMap D A ≫ Spec.algebraMap C D
    rw [Category.id_comp]
    change Spec.map (CommRingCat.ofHom (algebraMap C A)) =
      Spec.map (CommRingCat.ofHom (algebraMap D A)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap C D))
    rw [← Spec.map_comp]
    congr 1
    exact congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq C D A))

@[simp]
theorem ringTestRestrictScalarsIso_hom_left :
    (ringTestRestrictScalarsIso C D A).hom.left = 𝟙 _ := rfl

@[simp]
theorem ringTestRestrictScalarsIso_inv_left :
    (ringTestRestrictScalarsIso C D A).inv.left = 𝟙 _ := rfl

/-- The actual point equivalence induced by the pullback adjunction. -/
def ringPointBaseChangeEquiv (X : Over (Spec (CommRingCat.of C))) :
    RingPoint C X A ≃ RingPoint D (ringBaseChange C D X) A :=
  (Iso.homCongr (ringTestRestrictScalarsIso C D A).symm (Iso.refl X)).trans
    ((Over.mapPullbackAdj (Spec.algebraMap C D)).homEquiv (ringTest D A) X)

/-- In the inverse direction, forget the base change by its first projection. -/
@[simp]
theorem ringPointBaseChangeEquiv_symm_left
    (X : Over (Spec (CommRingCat.of C)))
    (p : RingPoint D (ringBaseChange C D X) A) :
    ((ringPointBaseChangeEquiv C D A X).symm p).left =
      p.left ≫ pullback.fst X.hom (Spec.algebraMap C D) := by
  change (𝟙 _ ≫ (p.left ≫ pullback.fst X.hom (Spec.algebraMap C D))) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

/-- A point and its base change have the same projection to the original scheme. -/
@[simp]
theorem ringPointBaseChangeEquiv_left_fst
    (X : Over (Spec (CommRingCat.of C))) (p : RingPoint C X A) :
    (ringPointBaseChangeEquiv C D A X p).left ≫
      pullback.fst X.hom (Spec.algebraMap C D) = p.left := by
  calc
    _ = ((ringPointBaseChangeEquiv C D A X).symm
        (ringPointBaseChangeEquiv C D A X p)).left :=
      (ringPointBaseChangeEquiv_symm_left C D A X _).symm
    _ = p.left := congrArg (fun q : RingPoint C X A => q.left)
      ((ringPointBaseChangeEquiv C D A X).symm_apply_apply p)

/-- The second projection of the base-changed point is its structure map. -/
@[simp]
theorem ringPointBaseChangeEquiv_left_snd
    (X : Over (Spec (CommRingCat.of C))) (p : RingPoint C X A) :
    (ringPointBaseChangeEquiv C D A X p).left ≫
      pullback.snd X.hom (Spec.algebraMap C D) = Spec.algebraMap D A :=
  Over.w (ringPointBaseChangeEquiv C D A X p)

/-- Base-change comparison is natural in the scheme. -/
theorem ringPointBaseChangeEquiv_natural
    {X Y : Over (Spec (CommRingCat.of C))} (f : X ⟶ Y) (p : RingPoint C X A) :
    ringPointBaseChangeEquiv C D A Y (p ≫ f) =
      ringPointBaseChangeEquiv C D A X p ≫
        (Over.pullback (Spec.algebraMap C D)).map f := by
  let p₀ : ringTest C A ⟶ X := p
  change ((Over.mapPullbackAdj (Spec.algebraMap C D)).homEquiv (ringTest D A) Y)
      ((ringTestRestrictScalarsIso C D A).hom ≫ (p₀ ≫ f) ≫ 𝟙 Y) =
    ((Over.mapPullbackAdj (Spec.algebraMap C D)).homEquiv (ringTest D A) X)
      ((ringTestRestrictScalarsIso C D A).hom ≫ p₀ ≫ 𝟙 X) ≫
        (Over.pullback (Spec.algebraMap C D)).map f
  simp only [Category.comp_id, ← Category.assoc]
  exact (Over.mapPullbackAdj (Spec.algebraMap C D)).homEquiv_naturality_right _ f

end Langlands.AlgebraicGeometry.PointTopology
