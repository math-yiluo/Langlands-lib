import Langlands.AlgebraicGeometry.ProjectiveSpace
import Langlands.AlgebraicGeometry.ModuleLinear
import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation

/-! # The morphism to projective space defined by finitely many sections -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Finitely many global sections `s 0, …, s n` of a line bundle `L` on a scheme `X` over a
field `K`, with no common zero at any point of `X`, define a morphism
`φ : X ⟶ ProjectiveSpace K n` over `Spec K`. On rational points and rational tangent vectors
this morphism is described by vanishing of the `K`-linear combinations
`∑ i, c i • s i`: two rational points have the same image exactly when every such
combination vanishing at the first also vanishes at the second, and a tangent vector at a
rational point `x` has the same image as the constant tangent vector at `x` exactly when
every such combination vanishing at `x` also vanishes along the tangent vector.
This proposition is a statement target, not a proof. -/
def LinearSystemMorphismStatement : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of K))
    (L : Picard.LineBundle X) (n : ℕ) (s : Fin (n + 1) → SchemeModule.GlobalSections L.obj),
    (∀ x : X, ∃ i, x ∈ SchemeModule.nonvanishingLocus L.obj (s i)) →
    ∃ φ : X ⟶ ProjectiveSpace K n, φ ≫ projectiveSpaceToSpec K n = p ∧
      (∀ x y : Spec (CommRingCat.of K) ⟶ X, Picard.IsRationalPoint p x →
        Picard.IsRationalPoint p y →
        (x ≫ φ = y ≫ φ ↔ ∀ c : Fin (n + 1) → K,
          Picard.VanishesAlong L x (∑ i, Scheme.Modules.scalarsFromBase p (c i) • s i) →
            Picard.VanishesAlong L y (∑ i, Scheme.Modules.scalarsFromBase p (c i) • s i))) ∧
      (∀ (x : Spec (CommRingCat.of K) ⟶ X) (t : Spec (CommRingCat.of (DualNumber K)) ⟶ X),
        Picard.IsRationalPoint p x → Picard.IsTangentVectorAt p x t →
        (t ≫ φ = (Picard.dualNumberProjection K ≫ x) ≫ φ ↔ ∀ c : Fin (n + 1) → K,
          Picard.VanishesAlong L x (∑ i, Scheme.Modules.scalarsFromBase p (c i) • s i) →
            Picard.VanishesAlong L t (∑ i, Scheme.Modules.scalarsFromBase p (c i) • s i)))

end Langlands.AlgebraicGeometry
