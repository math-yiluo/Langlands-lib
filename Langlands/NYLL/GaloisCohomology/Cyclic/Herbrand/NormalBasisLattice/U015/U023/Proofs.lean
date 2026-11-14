/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 187 on 2026-11-14: extracted M144.023, prefixed the
namespace with Langlands.NYLL, used the exact named statement target and
retained the local exponent argument. Source attribution and the
implemented proof adaptations are recorded in the paired Markdown.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.U021.Proofs

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel
open LocalFieldTheory

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- A common denominator exponent for products of finite generators (M144.023). -/
theorem exists_chosenBaseUniformizerPow_mul_mul_mem_of_fg_of_field_span_eq_top
    {M N P : Submodule 𝒪[K] L} (hN : N.FG) (hP : P.FG)
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) :
    exists_chosenBaseUniformizerPow_mul_mul_mem_of_fg_of_field_span_eq_topStatement K L hN hP hMspan := by
  change ∃ n : Nat, ∀ x : L, x ∈ N → ∀ y : L, y ∈ P →
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y) ∈ M
  rcases Submodule.fg_def.mp hN with ⟨S, hSfinite, hSspan⟩
  rcases Submodule.fg_def.mp hP with ⟨T, hTfinite, hTspan⟩
  let s : Finset L := hSfinite.toFinset
  let t : Finset L := hTfinite.toFinset
  let pairExp : L × L → Nat := fun p =>
    Classical.choose
      (exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_top
        (K := K) (L := L) hMspan (p.1 * p.2))
  let n : Nat := (s.product t).sup pairExp
  have hpair_spec (x y : L) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ (pairExp (x, y))) * (x * y) ∈ M :=
    Classical.choose_spec
      (exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_top
        (K := K) (L := L) hMspan (x * y))
  have hpow_mono {m : Nat} {z : L} (hmn : m ≤ n)
      (hz : algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * z ∈ M) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * z ∈ M := by
    rcases Nat.exists_eq_add_of_le hmn with ⟨d, hd⟩
    rw [hd]
    have hscaled :
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) *
            (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * z) ∈ M := by
      simpa [Algebra.smul_def, mul_assoc] using
        M.smul_mem (chosenIntegerRingUniformizer K ^ d) hz
    simpa [pow_add, map_mul, mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hgen (x y : L) (hxS : x ∈ S) (hyT : y ∈ T) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y) ∈ M := by
    have hxs : x ∈ s := (Set.Finite.mem_toFinset hSfinite).2 hxS
    have hyt : y ∈ t := (Set.Finite.mem_toFinset hTfinite).2 hyT
    exact hpow_mono (Finset.le_sup (Finset.mem_product.2 ⟨hxs, hyt⟩))
      (hpair_spec x y)
  have hleft (x : L) (hxS : x ∈ S) :
      ∀ y : L, y ∈ P →
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y) ∈ M := by
    intro y hyP
    rw [← hTspan] at hyP
    refine Submodule.span_induction
      (p := fun y _ =>
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y) ∈ M)
      ?hgen ?hzero ?hadd ?hsmul hyP
    · intro y hyT
      exact hgen x y hxS hyT
    · simp only [mul_zero, zero_mem]
    · intro y z _ _ hy hz
      simpa [mul_add] using M.add_mem hy hz
    · intro a y _ hy
      have hscaled :
          algebraMap 𝒪[K] L a *
              (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y)) ∈ M := by
        simpa [Algebra.smul_def, mul_assoc] using M.smul_mem a hy
      simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using hscaled
  refine ⟨n, ?_⟩
  intro x hxN y hyP
  rw [← hSspan] at hxN
  refine Submodule.span_induction
    (p := fun x _ =>
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y) ∈ M)
    ?gen ?zero ?add ?smul hxN
  · intro x hxS
    exact hleft x hxS y hyP
  · rw [zero_mul, mul_zero]
    exact M.zero_mem
  · intro x z _ _ hx hz
    convert M.add_mem hx hz using 1 ; ring
  · intro a x _ hx
    have hscaled :
        algebraMap 𝒪[K] L a *
            (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y)) ∈ M := by
      simpa [Algebra.smul_def, mul_assoc] using M.smul_mem a hx
    simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using hscaled

end
end Langlands.NYLL.CyclicCohomology
