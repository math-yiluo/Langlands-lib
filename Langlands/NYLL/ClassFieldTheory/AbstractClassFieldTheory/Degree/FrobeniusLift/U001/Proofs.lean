/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5168, 13 November 2026:
Extract the proof of M012.001 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusLift.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and state the theorem as the published proposition
exists_positive_nsmul_one_sub_mem_of_index_ne_zeroStatement applied to the
source parameters. The source proof rewrites with M009.012 and M009.010,
whose proofs are not yet published. That rewrite is replaced by applying
the private helper m012u001_mem_of_reduction_eq_zero (the kernel of
reduction modulo H.index lies in H). Its proof combines the second
inclusion of the source proof of M009.010 (ProfiniteInteger.lean, lines
149-172) with the inclusion of the H.index-multiples in H from M009.012
(lines 198-200), and reproves inline the closedness M009.006 (lines
105-108). The density M008.023 (ProfiniteIntegerCore.lean, lines 170-196)
and the integer-cast reduction M008.019 are reproved as private helpers for
the published closure model. The remaining tactic steps of the source
proof are kept unchanged. Import only the FrobeniusLift Statements module;
omit all other source declarations. The original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.Statements

/-!
# Positive natural representatives modulo finite-index subgroups of `ℤ̂`

Every class of a finite-index additive subgroup `H` of `ℤ̂` contains a
strictly positive natural multiple of `1`.
-/

namespace Langlands.NYLL.ClassFormation

open PortInternal.M008

noncomputable section

/-- Every point of the closure model lies in the closure of the integer casts. -/
private theorem m012u001_mem_closure_intCast (y : d007) :
    y ∈ closure (Set.range (fun a : ℤ => ((a : d007)))) := by
  rw [closure_subtype]
  have hval : ((↑) : d007 → d004) '' Set.range (fun a : ℤ => ((a : d007))) =
      (d006 : Set d004) := by
    ext v
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, rfl⟩
  rw [hval]
  exact y.2

/-- The ordinary integer casts are dense in `ℤ̂` (private copy of M008.023). -/
private theorem m012u001_denseRange_intCast : DenseRange (Int.cast : ℤ → ZHat) :=
  fun x => m012u001_mem_closure_intCast x

/-- Reduction of an ordinary integer cast (the content of M008.019). -/
private theorem m012u001_reduction_intCast (m : ℕ) (hm : 0 < m) (a : ℤ) :
    zHatReduction m hm (a : ZHat) = (a : ZMod m) := by
  have hredOne : zHatReduction m hm (1 : ZHat) = 1 := rfl
  rw [show (a : ZHat) = a • (1 : ZHat) from (zsmul_one a).symm, map_zsmul, hredOne,
    zsmul_one]

/-- An element of `ℤ̂` whose reduction modulo the finite index of `H` vanishes
lies in `H`. -/
private theorem m012u001_mem_of_reduction_eq_zero (H : AddSubgroup ZHat)
    (hm : 0 < H.index) (x : ZHat) (hx : zHatReduction H.index hm x = 0) : x ∈ H := by
  let U : Set ZHat := (zHatReduction H.index hm) ⁻¹' {0}
  have hU : IsOpen U := (isOpen_discrete _).preimage (map_continuous _)
  let C : Set ZHat := Set.range (fun y : ZHat => H.index • y)
  have hC : IsClosed C := (isCompact_range (continuous_id.nsmul H.index)).isClosed
  have hCH : C ⊆ H := by
    rintro _ ⟨y, rfl⟩
    exact H.nsmul_index_mem y
  have hUZ : U ∩ Set.range (Int.cast : ℤ → ZHat) ⊆ C := by
    rintro _ ⟨hu, a, rfl⟩
    have ha : ((a : ZMod H.index)) = 0 := by
      rw [← m012u001_reduction_intCast H.index hm a]
      exact hu
    obtain ⟨b, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a H.index).1 ha
    refine ⟨(b : ZHat), ?_⟩
    simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  have hxcl : x ∈ closure (U ∩ Set.range (Int.cast : ℤ → ZHat)) :=
    hU.inter_closure ⟨hx, m012u001_denseRange_intCast x⟩
  exact hCH (closure_minimal hUZ hC hxcl)

/-- In a finite cyclic quotient of `ℤ̂`, every class is represented by a
strictly positive natural multiple of `1`. -/
theorem exists_positive_nsmul_one_sub_mem_of_index_ne_zero
    (H : AddSubgroup ZHat) (hH : H.index ≠ 0) (z : ZHat) :
    exists_positive_nsmul_one_sub_mem_of_index_ne_zeroStatement H hH z := by
  show ∃ n : ℕ, 0 < n ∧ z - n • (1 : ZHat) ∈ H
  let m := H.index
  have hm : 0 < m := Nat.pos_of_ne_zero hH
  let r : ZMod m := zHatReduction m hm z
  let n : ℕ := r.val + m
  refine ⟨n, Nat.add_pos_right r.val hm, ?_⟩
  apply m012u001_mem_of_reduction_eq_zero H hm
  change zHatReduction m hm (z - n • (1 : ZHat)) = 0
  rw [map_sub, map_nsmul]
  have hredOne : zHatReduction m hm (1 : ZHat) = 1 :=
    rfl
  rw [hredOne]
  change zHatReduction m hm z - n • (1 : ZMod m) = 0
  rw [nsmul_eq_mul, mul_one]
  change r - (n : ZMod m) = 0
  have : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hn : (n : ZMod m) = r := by
    change ((r.val + m : ℕ) : ZMod m) = r
    rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero]
  rw [hn, sub_self]

end

end Langlands.NYLL.ClassFormation
