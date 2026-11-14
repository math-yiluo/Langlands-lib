/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 339 on 2026-11-14: extracted M144.026, prefixed the
namespace with Langlands.NYLL and used the exact named statement target.
Scalar-image membership and exponent monotonicity are proved locally,
without duplicating the adapted theorem names owned by the sibling task.
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

/-- At sufficient depth, lattice products land one uniformizer step deeper (M144.026). -/
theorem exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_succ_of_fg_of_field_span_eq_top
    {M : Submodule 𝒪[K] L} (hMfg : M.FG)
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) :
    exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_succ_of_fg_of_field_span_eq_topStatement
      K L hMfg hMspan := by
  change ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ x : L,
    x ∈ chosenBaseUniformizerPowSubmodule K L n M →
    ∀ y : L, y ∈ chosenBaseUniformizerPowSubmodule K L n M →
      x * y ∈ chosenBaseUniformizerPowSubmodule K L (n + 1) M
  have hmem (n : Nat) (x : L) :
      x ∈ chosenBaseUniformizerPowSubmodule K L n M ↔
        ∃ y : L, y ∈ M ∧
          algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y = x :=
    Iff.rfl
  have hmono {m n : Nat} {x : L} (hmn : m ≤ n)
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
  rcases exists_chosenBaseUniformizerPow_mul_mul_mem_of_fg_of_field_span_eq_top
      (K := K) (L := L) (M := M) (N := M) (P := M) hMfg hMfg hMspan with
    ⟨c, hc⟩
  refine ⟨c + 1, ?_⟩
  intro n hcn x hx y hy
  rcases Nat.exists_eq_add_of_le hcn with ⟨d, hd⟩
  rcases (hmem n x).1 hx with ⟨x0, hx0M, rfl⟩
  rcases (hmem n y).1 hy with ⟨y0, hy0M, rfl⟩
  have hprod :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ (c + d)) * (x0 * y0) ∈ M :=
    hmono (Nat.le_add_right c d) (hc x0 hx0M y0 hy0M)
  refine (hmem (n + 1) _).2 ?_
  refine ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ (c + d)) * (x0 * y0),
    hprod, ?_⟩
  rw [hd]
  simp only [map_mul, pow_add, pow_one]
  ring

end
end Langlands.NYLL.CyclicCohomology
