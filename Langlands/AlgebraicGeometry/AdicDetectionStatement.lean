import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Adic detection of a subscheme of a finite scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AdicDetection

/-- The canonical positive maximal-ideal thickening of the closed point. -/
def adicBase (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) :
    Spec (CommRingCat.of (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1))) ⟶
      Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))

/-- The underlying morphism of the base change of an actual scheme morphism over the base. -/
def baseChange {S X Z T : Scheme.{u}} (p : X ⟶ S) (i : Z ⟶ X) (r : T ⟶ S) :
    ((Over.pullback r).obj (Over.mk (i ≫ p))).left ⟶
      ((Over.pullback r).obj (Over.mk p)).left :=
  ((Over.pullback r).map
    (Over.homMk i (by simp) : Over.mk (i ≫ p) ⟶ Over.mk p)).left

/-- SGA 3, Exposé IX, Lemme 5.0: all positive adic thickenings detect the whole subscheme. -/
def AdicImmersionIsIsoStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (X Z : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of A)) (i : Z ⟶ X),
    IsFinite p → IsImmersion i →
    (∀ n : ℕ, IsIso (baseChange p i (adicBase A n))) → IsIso i

end Langlands.AlgebraicGeometry.AdicDetection
