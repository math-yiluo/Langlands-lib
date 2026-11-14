/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 187 on 2026-11-14: extracted M144.022, prefixed the
namespace with Langlands.NYLL, used the exact named statement target and
expanded scalar-image membership locally. Source attribution and the
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

/-- A common denominator exponent for a finitely generated submodule (M144.022). -/
theorem exists_chosenBaseUniformizerPowSubmodule_le_of_fg_of_field_span_eq_top
    {M N : Submodule 𝒪[K] L} (hN : N.FG)
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) :
    exists_chosenBaseUniformizerPowSubmodule_le_of_fg_of_field_span_eq_topStatement K L hN hMspan := by
  change ∃ n : Nat, chosenBaseUniformizerPowSubmodule K L n N ≤ M
  rcases Submodule.fg_def.mp hN with ⟨S, hSfinite, hSspan⟩
  let t : Finset L := hSfinite.toFinset
  let nOf : L → Nat := fun y =>
    Classical.choose
      (exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_top
        (K := K) (L := L) hMspan y)
  let n : Nat := t.sup nOf
  have hnOf_spec (y : L) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ nOf y) * y ∈ M :=
    Classical.choose_spec
      (exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_top
        (K := K) (L := L) hMspan y)
  have hpow_mono {m : Nat} {y : L} (hmn : m ≤ n)
      (hy : algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * y ∈ M) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ M := by
    rcases Nat.exists_eq_add_of_le hmn with ⟨d, hd⟩
    rw [hd]
    have hscaled :
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) *
            (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * y) ∈ M := by
      simpa [Algebra.smul_def, mul_assoc] using
        M.smul_mem (chosenIntegerRingUniformizer K ^ d) hy
    simpa [pow_add, map_mul, mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hN_mem (y : L) (hyN : y ∈ N) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ M := by
    rw [← hSspan] at hyN
    refine Submodule.span_induction
      (p := fun y _ =>
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ M)
      ?hgen ?hzero ?hadd ?hsmul hyN
    · intro y hyS
      have hyt : y ∈ t := by
        exact (Set.Finite.mem_toFinset hSfinite).2 hyS
      exact hpow_mono (Finset.le_sup hyt) (hnOf_spec y)
    · simp only [mul_zero, zero_mem]
    · intro y z _ _ hy hz
      simpa [mul_add] using M.add_mem hy hz
    · intro a y _ hy
      have hscaled :
          algebraMap 𝒪[K] L a *
              (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y) ∈ M := by
        simpa [Algebra.smul_def, mul_assoc] using M.smul_mem a hy
      simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using hscaled
  refine ⟨n, ?_⟩
  intro z hz
  change ∃ y : L, y ∈ N ∧
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y = z at hz
  rcases hz with
    ⟨y, hyN, rfl⟩
  exact hN_mem y hyN

end
end Langlands.NYLL.CyclicCohomology
