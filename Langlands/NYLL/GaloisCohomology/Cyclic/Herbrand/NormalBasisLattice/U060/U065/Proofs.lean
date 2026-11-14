/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Adapted by Worker 642 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
NormalBasisLattice.lean, lines 1191–1205. Namespace and imports are adapted;
the theorem is typed against the published Prop target. See the paired Markdown
for proof modifications. The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U060.Statements

namespace Langlands.NYLL.CyclicCohomology

open scoped ValuativeRel

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]

private theorem correctionPartialSum_mem_local
    {E : Submodule 𝒪[K] L}
    (hmul : ∀ x : L, x ∈ E → ∀ y : L, y ∈ E → x * y ∈ E)
    {x : L} (hx : x ∈ E) (d : Nat) :
    inverseCorrectionPartialSum (L := L) x d ∈ E := by
  have hn : -x ∈ E := E.neg_mem hx
  have hp : ∀ i : Nat, (-x) ^ (i + 1) ∈ E := by
    intro i
    induction i with
    | zero => simpa using hn
    | succ i ih =>
      rw [pow_succ]
      exact hmul _ ih _ hn
  unfold inverseCorrectionPartialSum
  exact E.sum_mem fun i _ => hp i

theorem chosenNormalBasisPrincipalUnitSet_inverseCorrectionPartialSum_mem {n : Nat}
    (hmul : ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L))
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) (d : Nat) :
    chosenNormalBasisPrincipalUnitSet_inverseCorrectionPartialSum_memStatement K L hmul hu d :=
  correctionPartialSum_mem_local K L hmul hu d

end Langlands.NYLL.CyclicCohomology
