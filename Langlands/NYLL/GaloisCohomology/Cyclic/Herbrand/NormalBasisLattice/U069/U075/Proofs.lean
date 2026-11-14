/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 518, 14 November 2026: extract M144.075 from NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace, narrow imports,
and give the theorem its unchanged published target. Inline the finite-sum
and closed-limit steps through a private helper with a distinct name.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U069.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U069.U073.Proofs

namespace Langlands.NYLL.CyclicCohomology

universe u
open LocalFieldTheory
open scoped ValuativeRel
open Filter

private theorem inverseCorrection_limit_mem
    (K L : Type u) [Field K] [Field L] [Algebra K L] [ValuativeRel K]
    [TopologicalSpace L] {E : Submodule 𝒪[K] L}
    (hclosed : IsClosed (E : Set L))
    (hmul : ∀ x : L, x ∈ E → ∀ y : L, y ∈ E → x * y ∈ E)
    {x z : L} (hx : x ∈ E)
    (hlim : Tendsto (fun d : Nat => inverseCorrectionPartialSum (L := L) x d)
      atTop (nhds z)) : z ∈ E := by
  apply hclosed.mem_of_tendsto hlim
  apply Eventually.of_forall
  intro d
  have hneg : -x ∈ E := E.neg_mem hx
  have hpow : ∀ i : Nat, (-x) ^ (i + 1) ∈ E := by
    intro i
    induction i with
    | zero => simpa only [Nat.zero_add, pow_one] using hneg
    | succ i ih =>
        simpa only [Nat.succ_add, pow_succ] using
          hmul ((-x) ^ (i + 1)) ih (-x) hneg
  unfold inverseCorrectionPartialSum
  exact E.sum_mem (fun i _ => hpow i)


theorem chosenNormalBasisPrincipalUnitSet_inverse_sub_one_mem_of_closed
    (K L : Type u)
    [Field K]
    [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]
    [ValuativeRel K]
    [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hclosed : IsClosed
      ((chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) : Set L)))
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    (hmul : ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈ chosenBaseUniformizerPowSubmodule K L n
            (chosenNormalBasisIntegerLattice K L))
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    chosenNormalBasisPrincipalUnitSet_inverse_sub_one_mem_of_closedStatement K L hclosed hle hmul hu := by
  change (((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) - 1 ∈
    chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)
  exact inverseCorrection_limit_mem K L hclosed hmul hu
    (chosenNormalBasisPrincipalUnitSet_inverseCorrection_tendsto_inv_sub_one
      K L hle hu)

end Langlands.NYLL.CyclicCohomology
