/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 519: extract M150.013 from NYLL fbd320cd,
-- use the exact published target, and prove the needed descending-filtration
-- argument privately. Identity membership and product recursion are unfolded.
-- See Proofs.md and licenses/NYLL/ for provenance and licensing.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.CorrectionProductLimitStatements

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section
universe u
open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel

private theorem m150_lattice_antitone
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (N : Submodule 𝒪[K] L) {m n : Nat} (hmn : m ≤ n) :
    chosenBaseUniformizerPowSubmodule K L n N ≤
      chosenBaseUniformizerPowSubmodule K L m N := by
  intro x hx
  change ∃ y : L, y ∈ N ∧
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y = x at hx
  rcases hx with ⟨y, hyN, rfl⟩
  rcases Nat.exists_eq_add_of_le hmn with ⟨d, hd⟩
  change ∃ w : L, w ∈ N ∧
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * w = _
  refine ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) * y, ?_, ?_⟩
  · simpa [Algebra.smul_def, mul_assoc] using
      N.smul_mem (chosenIntegerRingUniformizer K ^ d) hyN
  · simp [hd, pow_add, map_mul, mul_comm, mul_left_comm]

theorem chosenNormalBasisPrincipalUnitCorrectionProduct_mem
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] {n : Nat}
    (hmul : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u * v ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
    (d : Nat) :
    chosenNormalBasisPrincipalUnitCorrectionProduct_memStatement K L hmul z hz d := by
  change chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d ∈
    chosenNormalBasisPrincipalUnitSet K L n
  induction d with
  | zero =>
      change ((((1 : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) ∈
        chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)
      simpa using
        (chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)).zero_mem
  | succ d ih =>
      change chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d * z d ∈ _
      apply hmul _ ih (z d)
      exact m150_lattice_antitone K L (chosenNormalBasisIntegerLattice K L)
        (Nat.le_add_right n d) (hz d)

end
end Langlands.NYLL.LocalClassFieldTheory
