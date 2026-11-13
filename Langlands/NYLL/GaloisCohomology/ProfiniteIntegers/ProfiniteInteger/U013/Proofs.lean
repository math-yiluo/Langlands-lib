/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 135, 13 November 2026 UTC:
Prove M009.013 from
Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean
at fbd320cd8b1b06487c58227e92eb135794267709, adding the Langlands.NYLL
namespace prefix and importing only the published ProfiniteInteger
Statements module. The source proof (lines 219-221) substitutes the index
and applies M009.012, whose proof is not yet in the Library. This file
instead proves the target directly from the published closure model and
Mathlib. Three private lemmas restate, for this proof only, the source
facts it needs: density of the integer cast (M008.023), the inclusion
ker ⊆ range of M009.010 (by the source density argument, lines 149-172)
and the index computation of M009.011 (lines 175-189). The main proof
follows the source M009.012 argument (lines 198-212) with H.index
replaced by n through hindex. The original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements

/-!
# Additive subgroups of `ℤ̂` of a specified positive index

The exact proof of the published proposition M009.013: an additive subgroup
`H` of `ZHat` of index `n > 0` equals the image `n ℤ̂` of multiplication by
`n`. No closedness assumption on `H` is used.
-/

namespace Langlands.NYLL.ClassFormation

open PortInternal.M008

/-- The ordinary integers are dense in the closure model `ZHat`. -/
private theorem u013_denseRange_intCast : DenseRange (Int.castRingHom ZHat) := by
  have himg : Subtype.val '' Set.range (fun a : ℤ => (a : d007)) = (d006 : Set d004) := by
    ext y
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, rfl⟩
  have hd : Dense (Set.range (fun a : ℤ => (a : d007))) := by
    refine Topology.IsInducing.subtypeVal.dense_iff.mpr ?_
    intro x
    have hx : (x : d004) ∈ closure (d006 : Set d004) := x.2
    rw [← himg] at hx
    exact hx
  exact hd

/-- The kernel of reduction modulo `n` lies in the image of multiplication
by `n`. -/
private theorem u013_ker_le_range (n : ℕ) (hn : 0 < n) :
    (zHatReduction n hn).toAddMonoidHom.ker ≤ (zHatMulNat n).toAddMonoidHom.range := by
  intro y hy
  let K : Set ZHat := ((zHatReduction n hn).toAddMonoidHom.ker : Set ZHat)
  have hKopen : IsOpen K := by
    change IsOpen ((zHatReduction n hn) ⁻¹' ({0} : Set (ZMod n)))
    exact (isOpen_discrete _).preimage (map_continuous (zHatReduction n hn))
  have hclosed : IsClosed ((zHatMulNat n).toAddMonoidHom.range : Set ZHat) := by
    rw [AddMonoidHom.coe_range]
    exact (isCompact_range (map_continuous (zHatMulNat n))).isClosed
  have hKD : K ∩ Set.range (Int.castRingHom ZHat) ⊆
      ((zHatMulNat n).toAddMonoidHom.range : Set ZHat) := by
    rintro _ ⟨hzK, a, rfl⟩
    have ha0 : (a : ZMod n) = 0 := hzK
    obtain ⟨b, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a n).mp ha0
    refine ⟨(b : ZHat), ?_⟩
    change n • (b : ZHat) = (((n : ℤ) * b : ℤ) : ZHat)
    rw [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  exact closure_minimal hKD hclosed
    (u013_denseRange_intCast.open_subset_closure_inter hKopen hy)

/-- The image of multiplication by a positive `n` has additive index `n`. -/
private theorem u013_range_index (n : ℕ) (hn : 0 < n) :
    (zHatMulNat n).toAddMonoidHom.range.index = n := by
  have hrange : (zHatMulNat n).toAddMonoidHom.range =
      (zHatReduction n hn).toAddMonoidHom.ker := by
    refine le_antisymm ?_ (u013_ker_le_range n hn)
    rintro _ ⟨x, rfl⟩
    rw [AddMonoidHom.mem_ker]
    change zHatReduction n hn (n • x) = 0
    rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hsurj : Function.Surjective (zHatReduction n hn).toAddMonoidHom := by
    intro a
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
    exact ⟨(k : ZHat), rfl⟩
  rw [hrange, AddSubgroup.index,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv,
    Nat.card_zmod]

/-- Index-explicit form of the classification of finite-index additive
subgroups of `ℤ̂`. -/
theorem zHatAddSubgroup_eq_mulNat_range_of_index_eq
    (H : AddSubgroup ZHat) {n : ℕ} (hn : 0 < n) (hindex : H.index = n) :
    zHatAddSubgroup_eq_mulNat_range_of_index_eqStatement H hn hindex := by
  change H = (zHatMulNat n).toAddMonoidHom.range
  have hle : (zHatMulNat n).toAddMonoidHom.range ≤ H := by
    rintro _ ⟨x, rfl⟩
    have hx := H.nsmul_index_mem x
    rw [hindex] at hx
    exact hx
  have hrel : (zHatMulNat n).toAddMonoidHom.range.relIndex H = 1 := by
    have heq := AddSubgroup.relIndex_mul_index hle
    rw [u013_range_index n hn, hindex] at heq
    exact Nat.eq_of_mul_eq_mul_right hn (heq.trans (one_mul n).symm)
  exact le_antisymm (AddSubgroup.relIndex_eq_one.mp hrel) hle

end Langlands.NYLL.ClassFormation
