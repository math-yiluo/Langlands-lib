import Langlands.AlgebraicGeometry.Picard.MixedLineBundleEuler
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AbelianScheme.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Mixed Euler positivity for actual nonzero endomorphisms -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The actual mixed Euler coefficient of the pullback of an ample line bundle
by a nonzero endomorphism is positive in positive relative dimension. This is a
geometric proof target independent of the Rosati operation and trace. -/
def NonzeroEndomorphismMixedEulerPositiveStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (g : ℕ), 0 < g → A.HasRelativeDimension g →
    ∀ (L : LineBundle A.X.left), L.IsAmple →
    ∀ (f : A ⟶ A), f ≠ 0 →
      0 < mixedLineBundleEulerCoefficient A.X.hom L
        ((LineBundle.pullback (hom f)).obj L) g

end Langlands.AbelianScheme
