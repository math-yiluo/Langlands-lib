import Langlands.GroupScheme.Rational.RelativeWeylChamberGeneration
import Langlands.GroupScheme.Rational.WeylPositiveCocharacter
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Rational.CocharacterCentralizer

/-! # Trivial positive-root stabilizers by integral averaging -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- The subgroup of actual Weyl classes preserving the positive roots selected
by a cocharacter. -/
def positiveRootStabilizer (ν : cocharacterLattice T) : Subgroup (relativeWeylGroup i) where
  carrier := {w | ∀ α ∈ relativeRoots i,
    0 < latticePairing T (relativeWeylCharacterAction i w α) ν ↔
      0 < latticePairing T α ν}
  one_mem' := by
    intro α _
    rw [map_one]
    rfl
  mul_mem' := by
    intro w z hw hz α hα
    rw [map_mul, LinearEquiv.mul_apply]
    exact (hw _ (relativeWeylRootPermutation i z ⟨α, hα⟩).property).trans (hz α hα)
  inv_mem' := by
    intro w hw α hα
    have h := hw _ (relativeWeylRootPermutation i w⁻¹ ⟨α, hα⟩).property
    change 0 < latticePairing T
        (relativeWeylCharacterAction i w (relativeWeylCharacterAction i w⁻¹ α)) ν ↔
      0 < latticePairing T (relativeWeylCharacterAction i w⁻¹ α) ν at h
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
    exact h.symm

/-- A generic cocharacter has trivial actual positive-root stabilizer. The
finite stabilizer fixes its integral orbit sum, which is still generic. -/
theorem hasTrivialPositiveRootStabilizer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν) :
    HasTrivialPositiveRootStabilizer i ν := by
  classical
  let H := positiveRootStabilizer i ν
  let := hG.finite_relativeWeylGroup i hi
  let : Fintype H := Fintype.ofFinite H
  let νsum : cocharacterLattice T :=
    ∑ w : H, relativeWeylCocharacterAction i w.val ν
  have hνsumfixed (w : H) : relativeWeylCocharacterAction i w.val νsum = νsum := by
    dsimp only [νsum]
    rw [map_sum]
    simp_rw [← LinearEquiv.mul_apply, ← map_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft w) _ _ (fun _ => rfl)
  have hνsumgeneric : IsGenericCocharacter i νsum := by
    intro α hα
    have hsign (w : H) :
        0 < latticePairing T α (relativeWeylCocharacterAction i w.val ν) ↔
          0 < latticePairing T α ν := by
      rw [latticePairing_relativeWeyl_right]
      exact (H.inv_mem w.property) α hα
    have hnonzero (w : H) :
        latticePairing T α (relativeWeylCocharacterAction i w.val ν) ≠ 0 := by
      rw [latticePairing_relativeWeyl_right]
      exact hν _ (relativeWeylRootPermutation i w.val⁻¹ ⟨α, hα⟩).property
    change latticePairing T α (∑ w : H, relativeWeylCocharacterAction i w.val ν) ≠ 0
    rw [map_sum]
    rcases lt_or_gt_of_ne (hν α hα) with hneg | hpos
    · apply ne_of_lt
      apply Finset.sum_neg
      · intro w _
        have hs := hsign w
        have hn := hnonzero w
        omega
      · exact Finset.univ_nonempty
    · apply ne_of_gt
      apply Finset.sum_pos
      · intro w _
        exact (hsign w).mpr hpos
      · exact Finset.univ_nonempty
  intro w hw
  have hfixed := hνsumfixed ⟨w, hw⟩
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  have hz := (normalizerPoint_mem_dynamicCentralizer_iff i n νsum).mpr hfixed
  rw [genericCentralizer k G hG T i hi νsum hνsumgeneric, torusCentralizer_carrier_base] at hz
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hz

end Langlands.GroupScheme
