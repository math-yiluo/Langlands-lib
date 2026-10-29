import Langlands.AlgebraicGeometry.Picard.RelativePicardZero
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Constancy of the geometric Picard-zero condition on connected components -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- For a universal rigidified family over a field whose parameter scheme is locally of finite
type, if two actual geometric points of the parameter scheme have images in one connected
component and the family pulled back along the first is geometrically Picard-zero, then so is
the family pulled back along the second. -/
def FieldPicardZeroComponentConstancyStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (P : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (L : RigidifiedFamily A P),
    LocallyOfFiniteType P.hom →
      RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L →
        ∀ (x : P.left)
          (K₀ : Type u) [Field K₀] [IsAlgClosed K₀] (s₀ : Spec (CommRingCat.of K₀) ⟶ P.left)
          (K₁ : Type u) [Field K₁] [IsAlgClosed K₁] (s₁ : Spec (CommRingCat.of K₁) ⟶ P.left),
          Set.range s₀ ⊆ connectedComponent x →
          Set.range s₁ ⊆ connectedComponent x →
          IsPicardZeroFamily A
            ((RigidifiedLineBundle.relativePullback A.X.hom
              (unitSection A) (unitSection_comp A)
              (Over.homMk s₀ rfl : Over.mk (s₀ ≫ P.hom) ⟶ P)).obj L) →
          IsPicardZeroFamily A
            ((RigidifiedLineBundle.relativePullback A.X.hom
              (unitSection A) (unitSection_comp A)
              (Over.homMk s₁ rfl : Over.mk (s₁ ≫ P.hom) ⟶ P)).obj L)

end Langlands.AbelianScheme
