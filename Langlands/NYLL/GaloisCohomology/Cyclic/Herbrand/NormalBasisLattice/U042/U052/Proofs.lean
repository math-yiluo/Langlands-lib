/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 641 on 2026-11-14: extracted this proof into the
Langlands.NYLL namespace and made its exact published Statement the theorem
type. The paired Markdown records the proof and adaptations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U042.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U042.U043.Proofs

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel
open Filter LocalFieldTheory

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
variable [ValuativeRel K]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem exists_chosenBaseUniformizerPowSubmodule_le_integerRingFieldSubmodule_of_fg
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    {N : Submodule 𝒪[K] L} (hN : N.FG) :
    exists_chosenBaseUniformizerPowSubmodule_le_integerRingFieldSubmodule_of_fgStatement K L hN := by
  rcases Submodule.fg_def.mp hN with ⟨S, hSfinite, hSspan⟩
  let t : Finset L := hSfinite.toFinset
  let nOf : L → Nat := fun y =>
    Classical.choose
      (exists_chosenBaseUniformizerPow_mul_mem_integerRing_of_valuationExtension
        (K := K) (L := L) y)
  let n : Nat := t.sup nOf
  have hnOf_spec (y : L) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ nOf y) * y ∈ 𝒪[L] :=
    Classical.choose_spec
      (exists_chosenBaseUniformizerPow_mul_mem_integerRing_of_valuationExtension
        (K := K) (L := L) y)
  have hpow_mono {m : Nat} {y : L} (hmn : m ≤ n)
      (hy : algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * y ∈ 𝒪[L]) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ 𝒪[L] := by
    rcases Nat.exists_eq_add_of_le hmn with ⟨d, hd⟩
    have hd_mem :
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) ∈ 𝒪[L] := by
      change algebraMap K L ((chosenIntegerRingUniformizer K ^ d : 𝒪[K]) : K) ∈ 𝒪[L]
      exact (integerRingMapOfValuationExtension K L
        (chosenIntegerRingUniformizer K ^ d)).2
    rw [hd]
    rw [pow_add, map_mul]
    simpa [mul_assoc, mul_comm, mul_left_comm] using mul_mem hd_mem hy
  have hN_mem (y : L) (hyN : y ∈ N) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ 𝒪[L] := by
    rw [← hSspan] at hyN
    refine Submodule.span_induction
      (p := fun y _ =>
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ 𝒪[L])
      ?hgen ?hzero ?hadd ?hsmul hyN
    · intro y hyS
      have hyt : y ∈ t := by
        exact (Set.Finite.mem_toFinset hSfinite).2 hyS
      exact hpow_mono (Finset.le_sup hyt) (hnOf_spec y)
    · simp only [mul_zero, zero_mem]
    · intro y z _ _ hy hz
      simpa [mul_add] using add_mem hy hz
    · intro a y _ hy
      have ha_mem : algebraMap 𝒪[K] L a ∈ 𝒪[L] := by
        change algebraMap K L (a : K) ∈ 𝒪[L]
        exact (integerRingMapOfValuationExtension K L a).2
      simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using
        mul_mem ha_mem hy
  refine ⟨n, ?_⟩
  intro z hz
  rcases hz with ⟨y, hyN, rfl⟩
  exact hN_mem y hyN

end
end Langlands.NYLL.CyclicCohomology
