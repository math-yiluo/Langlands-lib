import Langlands.Galois.Local.LabelledHodgeTate

/-! # Tate's invariants of the completed algebraic closure and its twists -/

noncomputable section

universe u

namespace Langlands.GaloisRepresentation.HodgeTate

/-- Tate's fixed-field equality for the completed algebraic closure of a
finite extension of `ℚ_p`, and the vanishing of the fixed vectors in
every nonzero integral cyclotomic twist. -/
def TateTwistInvariantsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type u) [Field F]
    [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F],
    (∀ x : Completed p F,
      (∀ σ : Field.absoluteGaloisGroup F, galoisRingHom p σ x = x) ↔
        x ∈ (algebraMap F (Completed p F)).range) ∧
    ∀ (j : ℤ), j ≠ 0 → ∀ x : Completed p F,
      (∀ σ : Field.absoluteGaloisGroup F, cyclotomic p σ ^ j * galoisRingHom p σ x = x) →
      x = 0

end Langlands.GaloisRepresentation.HodgeTate
