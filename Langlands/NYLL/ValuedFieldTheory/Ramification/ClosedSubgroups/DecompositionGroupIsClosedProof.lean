/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 122, 2026-11-14: isolate the proof of M241.002
`decompositionGroup_isClosed` (lines 55–81 of
Nyll/ValuedFieldTheory/Ramification/ClosedSubgroups.lean) and the private
helper M241.001 `mem_decompositionGroup_iff_apply_mem` (lines 35–53) from
commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL. The helper keeps its private status, statement and proof; it
uses the section variables of line 32 only, so the section variable of
line 33 and the `omit ... in` of line 35 are dropped. The theorem is stated
as the published closed target `decompositionGroup_isClosedStatement`, so the
section variables and `A` are introduced in the proof and the original
`where isOpen_compl := ...` body becomes the structure instance
`{ isOpen_compl := ... }` with the same proof. The NYLL import of
RamificationGroup.lean is replaced by the published statement module, which
imports the published M239 data module and Mathlib.FieldTheory.Galois.Infinite.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.ClosedSubgroups.Statements

/-!
# finite Galois ramification theory: the decomposition group is closed (NYLL M241.002)

Each failure of `σ(A) = A` is witnessed by one field element `x`, hence persists on the coset
`σ · Fix(K(x))` of the open subgroup fixing the finite simple extension `K(x)`.
-/

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

universe u v

open scoped Pointwise Topology

section

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- NYLL M241.001 (private in the source and here): membership in the decomposition group
is preservation of membership in `A` by `σ`. -/
private theorem mem_decompositionGroup_iff_apply_mem
    (A : _root_.ValuationSubring L) (sigma : L ≃ₐ[K] L) :
    sigma ∈ decompositionGroup K A ↔
      ∀ x : L, sigma x ∈ A ↔ x ∈ A := by
  change sigma • A = A ↔ _
  constructor
  · intro hsigma x
    have hmem := congrArg (fun B : _root_.ValuationSubring L => sigma x ∈ B) hsigma
    change (sigma x ∈ sigma • A) = (sigma x ∈ A) at hmem
    rw [_root_.ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hmem
    change (sigma⁻¹ (sigma x) ∈ A) = (sigma x ∈ A) at hmem
    have hinv : sigma⁻¹ (sigma x) = x := sigma.symm_apply_apply x
    rw [hinv] at hmem
    exact hmem.symm.to_iff
  · intro hsigma
    ext x
    rw [_root_.ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    simpa using (hsigma (sigma⁻¹ x)).symm

end

/-- The valuation-subring decomposition group is closed in the Krull
topology. -/
theorem decompositionGroup_isClosed : decompositionGroup_isClosedStatement.{u, v} := by
  intro K L _ _ _ _ A
  exact
    { isOpen_compl := isOpen_iff_mem_nhds.mpr fun sigma hsigma => by
        rw [Set.mem_compl_iff, SetLike.mem_coe,
          mem_decompositionGroup_iff_apply_mem] at hsigma
        rcases Classical.not_forall.mp hsigma with ⟨x, hx⟩
        let E : IntermediateField K L := IntermediateField.adjoin K {x}
        let : FiniteDimensional K E :=
          IntermediateField.adjoin.finiteDimensional
            (Algebra.IsIntegral.isIntegral x)
        apply mem_nhds_iff.mpr
        refine ⟨sigma • (E.fixingSubgroup : Set (L ≃ₐ[K] L)), ?_, ?_, ?_⟩
        · intro tau htau
          rcases Set.mem_smul_set.mp htau with ⟨g, hg, rfl⟩
          rw [Set.mem_compl_iff, SetLike.mem_coe,
            mem_decompositionGroup_iff_apply_mem]
          intro hmem
          apply hx
          have hgx : g x = x :=
            (IntermediateField.mem_fixingSubgroup_iff E g).mp hg x
              (IntermediateField.subset_adjoin (F := K) (S := {x}) (Set.mem_singleton x))
          simpa [AlgEquiv.mul_apply, hgx] using hmem x
        · exact E.fixingSubgroup_isOpen.smul sigma
        · exact ⟨1, E.fixingSubgroup.one_mem, mul_one _⟩ }

end Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring
