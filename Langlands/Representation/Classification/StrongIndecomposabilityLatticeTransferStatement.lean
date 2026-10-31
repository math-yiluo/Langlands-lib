import Langlands.Representation.Classification.StrongIndecomposability

/-! # Generic lattice transport for strong indecomposability

These are algebraic interfaces for the essential highest-layer argument.
They assert no derivative, filtration or induced-product property.
-/

namespace Langlands.Classification

universe uK uG uH uV uW

/-- Transport through actual invariant-subspace lattices, including a
nonbottom essential subrepresentation identified with another such lattice. -/
def StrongIndecomposabilityLatticeTransferStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Group G] (H : Type uH) [Group H]
    (V : Type uV) [AddCommGroup V] [Module k V]
    (W : Type uW) [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (σ : Representation k H W),
    (∀ _e : Subrepresentation ρ ≃o Subrepresentation σ,
      IsStronglyIndecomposable ρ ↔ IsStronglyIndecomposable σ) ∧
    (∀ U : Subrepresentation ρ, U ≠ ⊥ →
      ∀ _e : Subrepresentation σ ≃o Set.Iic U,
        IsStronglyIndecomposable ρ ↔
          (∀ S : Subrepresentation ρ, S ≠ ⊥ → U ⊓ S ≠ ⊥) ∧
            IsStronglyIndecomposable σ)

end Langlands.Classification
