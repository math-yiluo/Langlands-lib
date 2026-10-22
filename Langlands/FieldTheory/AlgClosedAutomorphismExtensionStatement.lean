import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Extending automorphisms to algebraically closed extensions -/

namespace Langlands.FieldTheory

universe uF uOmega

/-- Every automorphism of a field extends to any algebraically closed field
containing it. The extension need not be algebraic. -/
def AlgClosedAutomorphismExtensionStatement : Prop :=
  ∀ (F : Type uF) [Field F] (Ω : Type uOmega) [Field Ω]
    [Algebra F Ω] [IsAlgClosed Ω] (e : F ≃+* F),
    ∃ σ : Ω ≃+* Ω, ∀ x : F,
      σ (algebraMap F Ω x) = algebraMap F Ω (e x)

end Langlands.FieldTheory
