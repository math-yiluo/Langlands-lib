import Langlands.GroupScheme.Rational.WeylPositiveCocharacter
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness
import Langlands.GroupScheme.Rational.RelativeRootNegationProof

/-! # Integral cocharacters presenting Weyl-stable root support -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.AbsoluteBorelOvergroup

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (j : T.toGrp ⟶ G) [Mono j.hom.hom.left] [IsAffineHom G.X.hom]

/-- The actual Weyl classes preserving membership in the specified set on
every actual root. No condition is imposed on nonroot characters. -/
def rootSupportStabilizer (S : Set (characterLattice T)) :
    Subgroup (relativeWeylGroup j) where
  carrier := {w | ∀ α ∈ roots j,
    relativeWeylCharacterAction j w α ∈ S ↔ α ∈ S}
  one_mem' := by
    intro α _
    rw [map_one]
    rfl
  mul_mem' := by
    intro w z hw hz α hα
    rw [map_mul, LinearEquiv.mul_apply]
    exact (hw _ (relativeWeylRootPermutation j z ⟨α, hα⟩).property).trans (hz α hα)
  inv_mem' := by
    intro w hw α hα
    have h := hw _ (relativeWeylRootPermutation j w⁻¹ ⟨α, hα⟩).property
    change relativeWeylCharacterAction j w
        (relativeWeylCharacterAction j w⁻¹ α) ∈ S ↔
      relativeWeylCharacterAction j w⁻¹ α ∈ S at h
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
    exact h.symm

/-- Finite integral averaging presents a root support by nonnegative pairings
when the positive roots of a generic cocharacter belong to it and every
symmetric root has a support-preserving Weyl negator. -/
theorem exists_cocharacter_of_finite_rootSupport_negators
    [Finite (relativeWeylGroup j)]
    (S : Set (characterLattice T))
    (hneg : ∀ α ∈ roots j, -α ∈ roots j)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter j ν)
    (hpos : ∀ α ∈ roots j, 0 < latticePairing T α ν → α ∈ S)
    (hflip : ∀ α ∈ roots j, α ∈ S → -α ∈ S →
      ∃ w : relativeWeylGroup j, relativeWeylCharacterAction j w α = -α ∧
        ∀ β ∈ roots j, relativeWeylCharacterAction j w β ∈ S ↔ β ∈ S) :
    ∃ ζ : cocharacterLattice T, ∀ α ∈ roots j,
      α ∈ S ↔ 0 ≤ latticePairing T α ζ := by
  classical
  let H := rootSupportStabilizer j S
  let : Fintype H := Fintype.ofFinite H
  let ζ : cocharacterLattice T :=
    ∑ w : H, relativeWeylCocharacterAction j w.val ν
  have hζfixed (w : H) : relativeWeylCocharacterAction j w.val ζ = ζ := by
    dsimp only [ζ]
    rw [map_sum]
    simp_rw [← LinearEquiv.mul_apply, ← map_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft w) _ _ (fun _ => rfl)
  have hnegative (α : characterLattice T) (hα : α ∈ roots j) (hαS : α ∉ S) :
      latticePairing T α ζ < 0 := by
    change latticePairing T α
      (∑ w : H, relativeWeylCocharacterAction j w.val ν) < 0
    rw [map_sum]
    apply Finset.sum_neg
    · intro w _
      rw [latticePairing_relativeWeyl_right]
      have hroot :
          relativeWeylCharacterAction j w.val⁻¹ α ∈ roots j :=
        (relativeWeylRootPermutation j w.val⁻¹ ⟨α, hα⟩).property
      have hnot : relativeWeylCharacterAction j w.val⁻¹ α ∉ S := by
        intro hw
        exact hαS (((H.inv_mem w.property) α hα).mp hw)
      have hn := hν _ hroot
      have hp : ¬ 0 < latticePairing T (relativeWeylCharacterAction j w.val⁻¹ α) ν :=
        fun h => hnot (hpos _ hroot h)
      omega
    · exact Finset.univ_nonempty
  refine ⟨ζ, ?_⟩
  intro α hα
  constructor
  · intro hαS
    by_cases hnαS : -α ∈ S
    · obtain ⟨w, hwα, hw⟩ := hflip α hα hαS hnαS
      have hp := latticePairing_relativeWeyl j w α ζ
      rw [hwα, hζfixed ⟨w, hw⟩, map_neg, LinearMap.neg_apply] at hp
      omega
    · have hn := hnegative (-α) (hneg α hα) hnαS
      rw [map_neg, LinearMap.neg_apply] at hn
      omega
  · intro hp
    by_contra hnot
    have hn := hnegative α hα hnot
    omega

/-- For a split maximal torus in a connected reductive group, proved
finiteness and root negation discharge the structural averaging inputs. -/
theorem exists_cocharacter_of_rootSupport_negators
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hj : IsMaximalTorus j)
    (S : Set (characterLattice T))
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter j ν)
    (hpos : ∀ α ∈ roots j, 0 < latticePairing T α ν → α ∈ S)
    (hflip : ∀ α ∈ roots j, α ∈ S → -α ∈ S →
      ∃ w : relativeWeylGroup j, relativeWeylCharacterAction j w α = -α ∧
        ∀ β ∈ roots j, relativeWeylCharacterAction j w β ∈ S ↔ β ∈ S) :
    ∃ ζ : cocharacterLattice T, ∀ α ∈ roots j,
      α ∈ S ↔ 0 ≤ latticePairing T α ζ := by
  let := hG.finite_relativeWeylGroup_of_isMaximalTorus j hj hT
  exact exists_cocharacter_of_finite_rootSupport_negators j S
    (fun _ hα => neg_mem_roots_of_split_maximalTorus hG hT j hj hα)
    ν hν hpos hflip

end Langlands.GroupScheme.AbsoluteBorelOvergroup
