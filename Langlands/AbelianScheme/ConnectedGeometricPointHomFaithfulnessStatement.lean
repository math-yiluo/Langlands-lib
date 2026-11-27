import Langlands.AbelianScheme.Basic
import Langlands.AbelianScheme.Tate.Integral
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Homomorphisms of abelian schemes over a connected base are detected at one geometric point -/

noncomputable section

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

universe u

namespace Langlands.AbelianScheme

/-- Over a connected locally noetherian base on which every positive integer is
a unit, a homomorphism of abelian schemes whose pullback to one algebraically
closed geometric point is zero is zero. -/
def ConnectedGeometricPointHomFaithfulnessStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] [ConnectedSpace S],
    (∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤))) →
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
      (A B : AbelianScheme S) (f : A ⟶ B),
      (baseChange s).map f = 0 → f = 0

end Langlands.AbelianScheme
