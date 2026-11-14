/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 187 on 2026-11-14: extracted M144.021 and a private
local adaptation of M144.017, prefixed the namespace with Langlands.NYLL,
used published dependencies and the exact named statement target.
The paired Markdown records the source correspondence and modifications.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U020.Proofs

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel
open LocalFieldTheory

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private theorem uniformizerPow_mul_mem_of_le
    {M : Submodule 𝒪[K] L} {m n : Nat} {x : L} (hmn : m ≤ n)
    (hx : algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * x ∈ M) :
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * x ∈ M := by
  rcases Nat.exists_eq_add_of_le hmn with ⟨d, hd⟩
  rw [hd]
  have hscaled :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) *
          (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * x) ∈ M := by
    simpa [Algebra.smul_def, mul_assoc] using
      M.smul_mem (chosenIntegerRingUniformizer K ^ d) hx
  simpa [pow_add, map_mul, mul_assoc, mul_comm, mul_left_comm] using hscaled

/-- Denominator clearing in a spanning integer-ring submodule (M144.021). -/
theorem exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_top
    {M : Submodule 𝒪[K] L}
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) (x : L) :
    exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_topStatement K L hMspan x := by
  change ∃ n : Nat, algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * x ∈ M
  have hx : x ∈ Submodule.span K ((M : Set L)) := by
    rw [hMspan]
    exact Submodule.mem_top
  refine Submodule.span_induction
    (p := fun y _ =>
      ∃ n : Nat, algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ M)
    ?hgen ?hzero ?hadd ?hsmul hx
  · intro y hyM
    refine ⟨0, ?_⟩
    simpa using hyM
  · refine ⟨0, ?_⟩
    rw [mul_zero]
    exact M.zero_mem
  · intro y z _ _ hy hz
    rcases hy with ⟨m, hm⟩
    rcases hz with ⟨n, hn⟩
    refine ⟨max m n, ?_⟩
    have hy' := uniformizerPow_mul_mem_of_le
      (K := K) (L := L) (M := M) (Nat.le_max_left m n) hm
    have hz' := uniformizerPow_mul_mem_of_le
      (K := K) (L := L) (M := M) (Nat.le_max_right m n) hn
    simpa [mul_add] using M.add_mem hy' hz'
  · intro c y _ hy
    rcases hy with ⟨m, hm⟩
    obtain ⟨d, hd⟩ := exists_chosenIntegerRingUniformizer_pow_mul_mem_integerRing K c
    let cInt : 𝒪[K] :=
      ⟨(((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ d) * c, hd⟩
    refine ⟨d + m, ?_⟩
    have hscaled :
        algebraMap 𝒪[K] L cInt *
            (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * y) ∈ M := by
      simpa [Algebra.smul_def, mul_assoc] using M.smul_mem cInt hm
    have hcInt :
        algebraMap 𝒪[K] L cInt =
          algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) *
            algebraMap K L c := by
      change algebraMap K L
          ((((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ d) * c) = _
      simp only [map_mul, map_pow]
      rfl
    rw [hcInt] at hscaled
    convert hscaled using 1
    rw [Algebra.smul_def, pow_add, map_mul]
    ring

end
end Langlands.NYLL.CyclicCohomology
