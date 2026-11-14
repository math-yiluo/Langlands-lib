/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 187 on 2026-11-14: extracted M144.025, prefixed the
namespace with Langlands.NYLL, used the exact named statement target,
expanded image membership and supplied a private adaptation of M144.017.
The paired Markdown records the source correspondence and modifications.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.U023.Proofs

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel
open LocalFieldTheory

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private theorem latticeProduct_pow_mul_mem_of_le
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

/-- Sufficiently deep uniformizer multiples of a spanning lattice are closed under products. -/
theorem exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_self_of_fg_of_field_span_eq_top
    {M : Submodule 𝒪[K] L} (hMfg : M.FG)
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) :
    exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_self_of_fg_of_field_span_eq_topStatement
      K L hMfg hMspan := by
  change ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ x : L,
    x ∈ chosenBaseUniformizerPowSubmodule K L n M →
    ∀ y : L, y ∈ chosenBaseUniformizerPowSubmodule K L n M →
      x * y ∈ chosenBaseUniformizerPowSubmodule K L n M
  rcases exists_chosenBaseUniformizerPow_mul_mul_mem_of_fg_of_field_span_eq_top
      (K := K) (L := L) (M := M) (N := M) (P := M) hMfg hMfg hMspan with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn x hx y hy
  change ∃ x0 : L, x0 ∈ M ∧
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * x0 = x at hx
  change ∃ y0 : L, y0 ∈ M ∧
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y0 = y at hy
  rcases hx with ⟨x0, hx0M, rfl⟩
  rcases hy with ⟨y0, hy0M, rfl⟩
  have hprod :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x0 * y0) ∈ M :=
    latticeProduct_pow_mul_mem_of_le (K := K) (L := L) hcn
      (hc x0 hx0M y0 hy0M)
  change ∃ z : L, z ∈ M ∧
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * z = _
  refine ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x0 * y0),
    hprod, ?_⟩
  simp [mul_assoc, mul_comm, mul_left_comm]

end
end Langlands.NYLL.CyclicCohomology
