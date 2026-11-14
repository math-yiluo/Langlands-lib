/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 519: extract M150.002 from NYLL fbd320cd,
-- prove the exact published target, and implement the further-scaling
-- containment privately. See Proofs.md and licenses/NYLL/.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.LatticeBoundStatements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.U001.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Proofs

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section
universe u
open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel

private theorem m150_lattice_further_scaling
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {N M : Submodule 𝒪[K] L} {a n : Nat}
    (h : chosenBaseUniformizerPowSubmodule K L a N ≤ M) :
    chosenBaseUniformizerPowSubmodule K L (a + n) N ≤
      chosenBaseUniformizerPowSubmodule K L n M := by
  intro x hx
  change ∃ y : L, y ∈ N ∧
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ (a + n)) * y = x at hx
  rcases hx with ⟨y, hyN, rfl⟩
  change ∃ w : L, w ∈ M ∧
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * w = _
  refine ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ a) * y, ?_, ?_⟩
  · exact h ⟨y, hyN, rfl⟩
  · simp [pow_add, map_mul, mul_assoc, mul_comm]

theorem chosenNormalBasisPrincipalUnitSet_mem_principalUnits_succ_of_lattice_bound
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    {b n i : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤ integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) {z : 𝒪[L]ˣ}
    (hz : z ∈ chosenNormalBasisPrincipalUnitSet K L (n + i)) :
    chosenNormalBasisPrincipalUnitSet_mem_principalUnits_succ_of_lattice_boundStatement
      K L hb hbn hz := by
  change z ∈ principalUnits L (1 + i)
  rcases Nat.exists_eq_add_of_le hbn with ⟨r, rfl⟩
  let x : L := ((((z : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L)
  have hxdeep : x ∈ chosenBaseUniformizerPowSubmodule K L
      (b + ((1 + r) + i)) (chosenNormalBasisIntegerLattice K L) := by
    simpa [x, Nat.add_assoc, chosenNormalBasisPrincipalUnitSet] using hz
  have hxint : x ∈ chosenBaseUniformizerPowSubmodule K L ((1 + r) + i)
      (integerRingFieldSubmodule K L) :=
    m150_lattice_further_scaling K L (a := b) (n := (1 + r) + i) hb hxdeep
  rcases chosenBaseUniformizerPow_integerRingFieldSubmodule_exists_mem_maximalIdeal_pow
      K L ((1 + r) + i) hxint with ⟨a, ha, hax⟩
  have hpow : (𝓂[L] ^ ((1 + r) + i) : Ideal 𝒪[L]) ≤
      (𝓂[L] ^ (1 + i) : Ideal 𝒪[L]) := by
    apply Ideal.pow_le_pow_right
    exact Nat.add_le_add_right (Nat.le_add_right 1 r) i
  have ha' : a ∈ (𝓂[L] ^ (1 + i) : Ideal 𝒪[L]) := hpow ha
  rw [mem_principalUnits_iff]
  have haeq : a = ((z : 𝒪[L]ˣ) : 𝒪[L]) - 1 := by
    apply Subtype.ext
    simpa [x] using hax
  simpa [haeq] using ha'

end
end Langlands.NYLL.LocalClassFieldTheory
