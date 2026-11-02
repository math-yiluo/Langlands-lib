import Mathlib.AlgebraicGeometry.PointsPi
import Mathlib.Algebra.Algebra.Pi

/-!
# Relative points over product rings

The points are actual morphisms in `Over (Spec C)`. The product comparison is
precomposition by the spectra of the coordinate projections, and forgetting the
base equation identifies it exactly with Mathlib's `AlgebraicGeometry.pointsPi`.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (C : Type u) [CommRing C]

/-- The actual spectrum of a `C`-algebra as a scheme over `Spec C`. -/
def ringTest (A : Type u) [CommRing A] [Algebra C A] :
    Over (Spec (CommRingCat.of C)) :=
  Over.mk (Spec.algebraMap C A)

/-- Actual `A`-valued points of a scheme over `Spec C`. -/
def RingPoint (X : Over (Spec (CommRingCat.of C)))
    (A : Type u) [CommRing A] [Algebra C A] :=
  ringTest C A ⟶ X

@[ext]
theorem RingPoint.ext {X : Over (Spec (CommRingCat.of C))}
    {A : Type u} [CommRing A] [Algebra C A] {p q : RingPoint C X A}
    (h : p.left = q.left) : p = q :=
  Over.OverMorphism.ext h

/-- Relative points are precisely the scheme morphisms satisfying the base equation. -/
def ringPointEquiv (X : Over (Spec (CommRingCat.of C)))
    (A : Type u) [CommRing A] [Algebra C A] :
    RingPoint C X A ≃
      {f : Spec (CommRingCat.of A) ⟶ X.left //
        f ≫ X.hom = Spec.algebraMap C A} where
  toFun p := ⟨p.left, Over.w p⟩
  invFun p := Over.homMk p.val p.property
  left_inv p := by rfl
  right_inv p := by rfl

/-- On an affine spectrum these points are the actual algebra homomorphisms. -/
def affineRingPointEquiv (B A : Type u) [CommRing B] [CommRing A]
    [Algebra C B] [Algebra C A] :
    RingPoint C (ringTest C B) A ≃ (B →ₐ[C] A) :=
  (ringPointEquiv C (ringTest C B) A).trans Spec.homEquivAlgHom

/-- An algebra map induces the contravariant morphism of spectra over the base. -/
def ringTestMap {A B : Type u} [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] (f : A →ₐ[C] B) :
    ringTest C B ⟶ ringTest C A :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact f.commutes c)

@[simp]
theorem ringTestMap_left {A B : Type u} [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] (f : A →ₐ[C] B) :
    (ringTestMap C f).left = Spec.map (CommRingCat.ofHom f.toRingHom) := rfl

@[simp]
theorem ringTestMap_id (A : Type u) [CommRing A] [Algebra C A] :
    ringTestMap C (AlgHom.id C A) = 𝟙 (ringTest C A) := by
  ext1
  exact Spec.map_id _

theorem ringTestMap_comp {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
    [Algebra C A] [Algebra C B] [Algebra C D]
    (f : A →ₐ[C] B) (g : B →ₐ[C] D) :
    ringTestMap C (g.comp f) = ringTestMap C g ≫ ringTestMap C f := by
  ext1
  change Spec.map (CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom g.toRingHom) =
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom)
  exact Spec.map_comp _ _

variable {C}

/-- Change of the value algebra, by precomposition on the actual relative points. -/
def RingPoint.changeRing {X : Over (Spec (CommRingCat.of C))}
    {A B : Type u} [CommRing A] [CommRing B] [Algebra C A] [Algebra C B]
    (f : A →ₐ[C] B) (p : RingPoint C X A) : RingPoint C X B :=
  ringTestMap C f ≫ p

variable (C) {ι : Type u} (R : ι → Type u)
variable [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]

/-- The map in Conrad (3.6.2), using the actual product algebra and actual scheme points. -/
def productPointMap (X : Over (Spec (CommRingCat.of C))) :
    RingPoint C X (∀ i, R i) → ∀ i, RingPoint C X (R i) :=
  fun p i => p.changeRing (Pi.evalAlgHom C R i)

/-- Forgetting the relative base equation gives exactly the Mathlib product-point map. -/
theorem productPointMap_underlying (X : Over (Spec (CommRingCat.of C)))
    (p : RingPoint C X (∀ i, R i)) :
    (fun i => (productPointMap C R X p i).left) =
      _root_.AlgebraicGeometry.pointsPi (fun i => CommRingCat.of (R i)) X.left p.left := rfl

/-- The component formula identifies the ring map and its direction explicitly. -/
@[simp]
theorem productPointMap_left (X : Over (Spec (CommRingCat.of C)))
    (p : RingPoint C X (∀ i, R i)) (i : ι) :
    (productPointMap C R X p i).left =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom R i)) ≫ p.left := rfl

/-- Product comparison commutes with morphisms of schemes over the base. -/
theorem productPointMap_natural {X Y : Over (Spec (CommRingCat.of C))}
    (f : X ⟶ Y) (p : RingPoint C X (∀ i, R i)) (i : ι) :
    productPointMap C R Y (p ≫ f) i = productPointMap C R X p i ≫ f :=
  (Category.assoc _ _ _).symm

end Langlands.AlgebraicGeometry.PointTopology
