/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 111, 13 November 2026:
Prove the published target of M009.014 from
Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and import only the published ProfiniteInteger Statements module.
Because the source prerequisites have no published proofs, port the
source proofs of ProfiniteIntegerCore.denseRange_intCast_zHat and of
ProfiniteInteger M009.006, M009.008, M009.009, M009.010, M009.011 and
M009.012 as helper theorems in Langlands.NYLL.PortInternal.M009U014, over
the published closure-model names d004, d005 and d006. Small proof edits
are recorded in the paired Markdown. The original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements

/-!
# Finite-quotient subgroups of the NYLL profinite integers

Every additive subgroup `H` of `ZHat` with finite quotient equals the image
of multiplication by its index. The local helpers port the source proofs
that the integers are dense, that `n ZHat` is closed and equals the kernel of
reduction modulo `n`, and that it has index `n`.
-/

namespace Langlands.NYLL.PortInternal.M009U014

open Langlands.NYLL.ClassFormation Langlands.NYLL.PortInternal.M008

noncomputable section

/-- The ordinary integers have dense image in their profinite completion.
(Port of the source `ClassFormation.denseRange_intCast_zHat`.) -/
theorem denseRange_intCast_zHat :
    DenseRange (Int.castRingHom ZHat) := by
  have hinclusion : DenseRange
      (Set.inclusion (Subring.le_topologicalClosure d006)) := by
    apply (denseRange_inclusion_iff
      (Subring.le_topologicalClosure d006)).2
    change closure (d006 : Set d004) ⊆
      closure (d006 : Set d004)
    exact Set.Subset.rfl
  have hdiagonal : DenseRange d005.rangeRestrict :=
    d005.rangeRestrict_surjective.denseRange
  have hcomp : DenseRange
      (Set.inclusion (Subring.le_topologicalClosure d006) ∘
        d005.rangeRestrict) :=
    hinclusion.comp hdiagonal
      (continuous_inclusion
        (Subring.le_topologicalClosure d006))
  have heq :
      Set.inclusion (Subring.le_topologicalClosure d006) ∘
          d005.rangeRestrict =
        (fun a : ℤ => Int.castRingHom ZHat a) := by
    funext a
    apply Subtype.ext
    funext i
    rfl
  rw [heq] at hcomp
  exact hcomp

/-- The image `n ℤ̂` is closed. (Port of the source M009.006.) -/
theorem isClosed_zHatMulNat_range (n : ℕ) :
    IsClosed ((zHatMulNat n).toAddMonoidHom.range : Set ZHat) := by
  rw [AddMonoidHom.coe_range]
  exact (isCompact_range (map_continuous (zHatMulNat n))).isClosed

/-- Reduction modulo a positive integer is onto. (Port of the source
M009.008.) -/
theorem zHatReduction_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (zHatReduction n hn) := by
  intro a
  rcases ZMod.intCast_surjective a with ⟨a, rfl⟩
  exact ⟨(Int.castRingHom ZHat) a, rfl⟩

/--
Establishes the identity `zHatMulNat n ((Int.castRingHom ZHat) a) = (Int.castRingHom ZHat) ((n :
ℤ) * a)`.
(Port of the source M009.009, proved through the ring structure instead of
`ZHat.ext`.)
-/
theorem zHatMulNat_int (n : ℕ) (a : ℤ) :
    zHatMulNat n ((Int.castRingHom ZHat) a) =
      (Int.castRingHom ZHat) ((n : ℤ) * a) := by
  change n • (Int.castRingHom ZHat) a = (Int.castRingHom ZHat) ((n : ℤ) * a)
  rw [map_mul, map_natCast, nsmul_eq_mul]

/-- The subgroup `n ℤ̂` is exactly the kernel of reduction modulo `n`.
(Port of the source M009.010.) -/
theorem zHatMulNat_range_eq_ker_reduction (n : ℕ) (hn : 0 < n) :
    (zHatMulNat n).toAddMonoidHom.range =
      (zHatReduction n hn).toAddMonoidHom.ker := by
  apply AddSubgroup.ext
  intro y
  constructor
  · rintro ⟨x, rfl⟩
    change zHatReduction n hn (zHatMulNat n x) = 0
    change n • zHatReduction n hn x = 0
    simp [nsmul_eq_mul]
  · intro hy
    let K : Set ZHat :=
      ((zHatReduction n hn).toAddMonoidHom.ker : Set ZHat)
    let D : Set ZHat :=
      Set.range (Int.castRingHom ZHat)
    have hKopen : IsOpen K := by
      change IsOpen ((zHatReduction n hn) ⁻¹' ({0} : Set (ZMod n)))
      have hzeroOpen : IsOpen ({0} : Set (ZMod n)) := isOpen_discrete _
      exact hzeroOpen.preimage (map_continuous (zHatReduction n hn))
    have hDdense : Dense D := by
      exact denseRange_intCast_zHat
    have hKD : K ∩ D ⊆
        ((zHatMulNat n).toAddMonoidHom.range : Set ZHat) := by
      rintro _ ⟨hzK, a, rfl⟩
      have ha0 : (a : ZMod n) = 0 := hzK
      have hna : (n : ℤ) ∣ a :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd a n).mp ha0
      rcases hna with ⟨b, rfl⟩
      refine ⟨(Int.castRingHom ZHat) b, ?_⟩
      exact zHatMulNat_int n b
    have hyClosure : y ∈ closure (K ∩ D) :=
      (hDdense.open_subset_closure_inter hKopen) hy
    exact (closure_minimal hKD (isClosed_zHatMulNat_range n)) hyClosure

/-- The additive index of `n ℤ̂` in `ℤ̂` is `n`. (Port of the source
M009.011.) -/
theorem zHatMulNat_range_index (n : ℕ) (hn : 0 < n) :
    (zHatMulNat n).toAddMonoidHom.range.index = n := by
  let : NeZero n := ⟨hn.ne'⟩
  rw [zHatMulNat_range_eq_ker_reduction n hn,
    AddSubgroup.index_ker]
  rw [AddMonoidHom.range_eq_top_of_surjective
    (zHatReduction n hn).toAddMonoidHom (zHatReduction_surjective n hn)]
  calc
    Nat.card (↑(⊤ : AddSubgroup (ZMod n))) = Nat.card (ZMod n) :=
      Nat.card_congr
        { toFun := fun x => x.1
          invFun := fun x => ⟨x, AddSubgroup.mem_top x⟩
          left_inv := fun x => Subtype.ext rfl
          right_inv := fun _ => rfl }
    _ = n := Nat.card_zmod n

/-- Every additive subgroup of finite nonzero index in `ℤ̂` is the expected
principal subgroup.  Closedness is not needed: the quotient is abelian, so its
cardinality annihilates every quotient class, and comparison of indices forces
equality. (Port of the source M009.012.) -/
theorem zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero
    (H : AddSubgroup ZHat) (hH : H.index ≠ 0) :
    H = (zHatMulNat H.index).toAddMonoidHom.range := by
  have hle : (zHatMulNat H.index).toAddMonoidHom.range ≤ H := by
    rintro y ⟨x, rfl⟩
    exact H.nsmul_index_mem x
  have hrangeIndex :
      (zHatMulNat H.index).toAddMonoidHom.range.index = H.index :=
    zHatMulNat_range_index H.index (Nat.pos_of_ne_zero hH)
  have hrel :
      (zHatMulNat H.index).toAddMonoidHom.range.relIndex H = 1 := by
    have heq :
        (zHatMulNat H.index).toAddMonoidHom.range.relIndex H * H.index =
          H.index :=
      (AddSubgroup.relIndex_mul_index hle).trans hrangeIndex
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hH)
    simpa only [one_mul] using heq
  exact le_antisymm (AddSubgroup.relIndex_eq_one.mp hrel) hle

end

end Langlands.NYLL.PortInternal.M009U014

namespace Langlands.NYLL.ClassFormation

/-- A subgroup with finite quotient is the subgroup obtained by multiplying by
its index. -/
theorem zHatAddSubgroup_eq_mulNat_range_of_finite_quotient
    (H : AddSubgroup ZHat) [Finite (ZHat ⧸ H)] :
    zHatAddSubgroup_eq_mulNat_range_of_finite_quotientStatement H :=
  PortInternal.M009U014.zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero H
    H.index_ne_zero_of_finite

end Langlands.NYLL.ClassFormation
