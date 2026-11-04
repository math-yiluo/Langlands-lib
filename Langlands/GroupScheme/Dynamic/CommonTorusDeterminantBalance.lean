import Langlands.GroupScheme.Dynamic.RootSystemDeterminantRestriction
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Dimension-weighted root-sign balance for a common split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators Classical

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

/-- The sum of the actual adjoint weights in a specified region, with their
actual weight-space dimensions as multiplicities. -/
def regionWeightCharacter (p : characterLattice T → Prop) :
    rationalCharacters T.toGrp := by
  classical
  exact ∑ᶠ α : characterLattice T,
    (if p α then Module.finrank k (weightSpace i α) else 0) •
      (rationalCharacters.equivCharacterLattice T).symm α

section Finite

variable [LocallyOfFiniteType G.X.hom] (hT : IsSplitTorus T.toGrp)

private theorem regionWeightCharacter_eq_sum (p : characterLattice T → Prop) :
    regionWeightCharacter i p =
      ∑ α ∈ (hT.finite_weightSupport i).toFinset,
        (if p α then Module.finrank k (weightSpace i α) else 0) •
          (rationalCharacters.equivCharacterLattice T).symm α := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro α hα
  rw [Set.Finite.coe_toFinset]
  intro hb
  have hd : Module.finrank k (weightSpace i α) = 0 := by rw [hb, finrank_bot]
  exact hα (by simp only [hd, ite_self, zero_smul])

include hT in
/-- Partition a positive region according to the sign of a second pairing. -/
theorem regionWeightCharacter_positive_partition
    (ζ eta : cocharacterLattice T) :
    positiveWeightCharacter i ζ =
      regionWeightCharacter i
        (fun α => 0 < latticePairing T α ζ ∧ latticePairing T α eta = 0) +
      regionWeightCharacter i
        (fun α => 0 < latticePairing T α ζ ∧ 0 < latticePairing T α eta) +
      regionWeightCharacter i
        (fun α => 0 < latticePairing T α ζ ∧ latticePairing T α eta < 0) := by
  classical
  have hpos : positiveWeightCharacter i ζ =
      regionWeightCharacter i (fun α => 0 < latticePairing T α ζ) := by
    unfold positiveWeightCharacter regionWeightCharacter
    apply finsum_congr
    intro α
    split_ifs <;> rfl
  rw [hpos]
  simp only [regionWeightCharacter_eq_sum i hT, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  by_cases hζ : 0 < latticePairing T α ζ
  · rcases lt_trichotomy (latticePairing T α eta) 0 with heta | heta | heta
    · simp [hζ, heta, ne_of_lt heta, not_lt_of_ge heta.le]
    · simp [hζ, heta]
    · simp [hζ, heta, ne_of_gt heta, not_lt_of_ge heta.le]
  · simp [hζ]

end Finite

section Negation

variable {i}

variable [Mono i.hom.hom.left]
  (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)

include hroot hT

/-- Negating a region negates its dimension-weighted character. -/
theorem HasRelativeRootSystem.regionWeightCharacter_neg
    (p : characterLattice T → Prop) :
    regionWeightCharacter i (fun α => p (-α)) = -regionWeightCharacter i p := by
  classical
  unfold regionWeightCharacter
  rw [← finsum_comp_equiv (Equiv.neg (characterLattice T)), ← finsum_neg_distrib]
  apply finsum_congr
  intro α
  simp only [Equiv.neg_apply, neg_neg, map_neg, smul_neg]
  change -((if p α then Module.finrank k (weightSpace i (-α)) else 0) •
    (rationalCharacters.equivCharacterLattice T).symm α) = _
  rw [hroot.finrank_weightSpace_neg hT]

/-- The two mixed-sign regions cancel with their actual root multiplicities. -/
theorem HasRelativeRootSystem.mixedWeightCharacter_add_eq_zero
    (ζ eta : cocharacterLattice T) :
    regionWeightCharacter i
        (fun α => 0 < latticePairing T α ζ ∧ latticePairing T α eta < 0) +
      regionWeightCharacter i
        (fun α => latticePairing T α ζ < 0 ∧ 0 < latticePairing T α eta) = 0 := by
  have h := hroot.regionWeightCharacter_neg hT
    (fun α => 0 < latticePairing T α ζ ∧ latticePairing T α eta < 0)
  simp only [map_neg, LinearMap.neg_apply, neg_pos, neg_lt_zero] at h
  rw [h, add_neg_cancel]

variable [LocallyOfFiniteType G.X.hom]

/-- The exact dimension-weighted sign balance for two arbitrary cocharacters
of the same split torus. Both axis regions are retained. -/
theorem HasRelativeRootSystem.positiveWeightCharacter_balance
    (ζ eta : cocharacterLattice T) :
    positiveWeightCharacter i ζ + positiveWeightCharacter i eta =
      regionWeightCharacter i
        (fun α => 0 < latticePairing T α ζ ∧ latticePairing T α eta = 0) +
      regionWeightCharacter i
        (fun α => latticePairing T α ζ = 0 ∧ 0 < latticePairing T α eta) +
      2 • regionWeightCharacter i
        (fun α => 0 < latticePairing T α ζ ∧ 0 < latticePairing T α eta) := by
  rw [regionWeightCharacter_positive_partition i hT ζ eta,
    regionWeightCharacter_positive_partition i hT eta ζ]
  have hswap (p q : characterLattice T → Prop) :
      regionWeightCharacter i (fun α => p α ∧ q α) =
        regionWeightCharacter i (fun α => q α ∧ p α) := by
    congr 1
    funext α
    exact propext (and_comm ..)
  rw [hswap (fun α => 0 < latticePairing T α eta)
      (fun α => latticePairing T α ζ = 0),
    hswap (fun α => 0 < latticePairing T α eta)
      (fun α => 0 < latticePairing T α ζ),
    hswap (fun α => 0 < latticePairing T α eta)
      (fun α => latticePairing T α ζ < 0)]
  have hc := hroot.mixedWeightCharacter_add_eq_zero hT ζ eta
  rw [add_eq_zero_iff_eq_neg] at hc
  rw [hc, two_smul]
  abel

end Negation

end Langlands.GroupScheme
