import Langlands.AbelianScheme.IsogenySpecialization
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Surjective endomorphisms of abelian varieties are isogenies -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Let `α` be an endomorphism of an abelian scheme `A` over an algebraically closed field
`k`. If the underlying scheme morphism of `α` is surjective, then `α` is an isogeny, that is,
finite, flat and surjective. This proposition is a statement target, not a proof. -/
def FieldSurjectiveEndomorphismIsogenyStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (α : A ⟶ A), Surjective (hom α) → IsIsogeny α

end Langlands.AbelianScheme
