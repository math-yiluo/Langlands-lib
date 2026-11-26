import Langlands.AbelianScheme.RationalTorsionExtension
import Langlands.AbelianScheme.NeronModelExistenceStatement
import Langlands.AbelianScheme.SemistableReductionConstruction

/-! # Potential semiabelian reduction from Néron existence and Raynaud's criterion

`PotentialSemistableReductionFromRaynaudStatement` says that existence of Néron models
(`NeronModelExistenceStatement`) and Raynaud's criterion
(`RaynaudSemiabelianCriterionStatement`) imply potential semiabelian reduction
(`PotentialSemistableReductionStatement`), at the same universe.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Néron existence and Raynaud's criterion imply potential semiabelian reduction. -/
def PotentialSemistableReductionFromRaynaudStatement : Prop :=
  NeronModelExistenceStatement.{u} → RaynaudSemiabelianCriterionStatement.{u} →
    PotentialSemistableReductionStatement.{u}

/-- In a local ring, `3` or `4` is a unit. -/
theorem exists_three_le_isUnit_natCast (V : Type u) [CommRing V] [IsLocalRing V] :
    ∃ n : ℕ, 3 ≤ n ∧ IsUnit (n : V) := by
  by_cases h3 : IsUnit ((3 : ℕ) : V)
  · exact ⟨3, le_rfl, h3⟩
  · refine ⟨4, by norm_num, ?_⟩
    have h1 : IsUnit (((4 : ℕ) : V) + -((3 : ℕ) : V)) := by
      have : ((4 : ℕ) : V) + -((3 : ℕ) : V) = 1 := by push_cast; ring
      rw [this]
      exact isUnit_one
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h | h
    · exact h
    · exact absurd ((IsUnit.neg_iff _).mp h) h3

/-- Proof of the reduction: choose `n ∈ {3, 4}` invertible in the valuation ring, make the
`n`-torsion rational over a finite extension, take a Néron model over a dominating
valuation ring of that extension and apply Raynaud's criterion there. -/
theorem potentialSemistableReductionFromRaynaud :
    PotentialSemistableReductionFromRaynaudStatement.{u} := by
  intro hN hR V K _ _ _ _ _ _ B
  obtain ⟨n, hn3, hnV⟩ := exists_three_le_isUnit_natCast V
  have hnK : IsUnit (n : K) := by simpa using hnV.map (algebraMap V K)
  obtain ⟨L, _, _, hL, htor⟩ :=
    exists_finite_hasRationalGeometricTorsion K B n (by omega) hnK
  let E := FiniteDvrExtension.ofFiniteField V K L
  have hnE : IsUnit (n : E.ring) := by simpa using hnV.map (algebraMap V E.ring)
  obtain ⟨N⟩ := hN E.ring E.fractionField
    ((baseChange (Spec.algebraMap K E.fractionField)).obj B)
  exact ⟨E, N, hR E.ring E.fractionField _ N n hn3 hnE htor⟩

end Langlands.AbelianScheme
