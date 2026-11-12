import Langlands.Algebra.NonUnitalModuleDualCompletion

/-! # The completion of the nondegenerate dual is the full dual (Renard I.4.3)

For a complex algebra with idempotents `A` and a nondegenerate `A`-module `M`, the completion
of the nondegenerate dual `M̃` is the full dual `M*`: the two published maps between `M*` and
the compatible families of vectors of `M̃` are inverse to each other.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDualCompletion

open NonUnitalModuleDual (FullDual Dual)

universe uA uM

attribute [local instance] NonUnitalModuleDual.fullAction NonUnitalModuleDual.dualAction

/-- Renard I.4.3, conclusion `completion(M̃) = completion((M^*)_A) ≃ M^*`. Let `A` be a complex algebra
with idempotents and `M` a nondegenerate `A`-module, with its canonical complex scalars. The
published map `toCompletion` sends a linear form `φ ∈ M^*` to the compatible family
`(e • φ)_e` of vectors of the nondegenerate dual `M̃`, and `toFullDual` sends a compatible
family `x` to the form `m ↦ x(e)(m)` for any idempotent `e` fixing `m`. These two maps are
inverse to each other. Both are `A`-module maps (published `toCompletionHom`,
`toFullDualHom`), so this is an isomorphism of right `A`-modules between the completion of
`M̃` and `M^*`. -/
def DualCompletionStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M),
    (∀ φ : FullDual hA hM, toFullDual hA hM (toCompletion hA hM φ) = φ) ∧
    ∀ x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM),
      toCompletion hA hM (toFullDual hA hM x) = x

end Langlands.Algebra.NonUnitalModuleDualCompletion
