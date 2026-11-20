import Langlands.GroupScheme.Rational.CocharacterCone

/-! # The threshold partition of the integral cocharacter cone -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

namespace Langlands.GroupScheme.CocharacterCone

/-- The corrected finite-residue threshold partition used in the proof of
Renard VII.1.2, on the existing nonnegative cocharacter quotient. -/
def ThresholdPartitionStatement : Prop :=
  ∀ (k : Type u) [Field k] (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (R : Set (characterLattice T)) [Fintype R] [DecidableEq R]
    (ray : R → cocharacterLattice T),
    (∀ α, 0 < latticePairing T α.val (ray α)) →
    (∀ α β, β ≠ α → latticePairing T β.val (ray α) = 0) →
    let A := RealTorusSpace.rootAnnihilatorInt T R
    let residues := A.mkQ '' {c | ∀ α : R,
      0 ≤ latticePairing T α.val c ∧ latticePairing T α.val c < latticePairing T α.val (ray α)}
    residues.Finite ∧
    ∀ n : ℕ,
      ∃ e : (Σ J : Finset R, residues × (↥J → Fin (n + 1)) ×
          ({α : R // α ∉ J} → ℕ)) ≃ quotient T R,
        ∀ p,
          let J := p.1
          let r := p.2.1
          let bounded := p.2.2.1
          let tail := p.2.2.2
          (e p).val = r.val + A.mkQ (∑ α : R,
            (if h : α ∈ J then (bounded ⟨α, h⟩ : ℕ) else n + 1 + tail ⟨α, h⟩) • ray α)

end Langlands.GroupScheme.CocharacterCone
