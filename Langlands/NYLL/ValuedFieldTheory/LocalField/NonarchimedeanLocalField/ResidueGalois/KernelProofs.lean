/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois.KernelStatements

/-!
# The two residue-kernel characterizations

Adapted by Worker 84 from NYLL M160.017 and M160.018 on 29 October 2026.
Each theorem proves its own published closed target over an arbitrary shared
universe. The first uses the published residue evaluation and quotient
surjectivity; the second uses the maximal-ideal kernel of the residue map.
See the paired Markdown for source correspondence and modifications.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The actual residue kernel consists exactly of automorphisms preserving the
residue of every integer. This proves the closed target for NYLL M160.017. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_residue_eq :
    GaloisGroupResidueAlgEquivHomOfIsIntegralClosureMemKerIffResidueEqStatement.{u} := by
  intro K L _ _ _ _ _ _ _ σ
  rw [MonoidHom.mem_ker]
  constructor
  · intro h x
    have hx := congrArg (fun e : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] =>
      e (IsLocalRing.residue 𝒪[L] x)) h
    change galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ
        (IsLocalRing.residue 𝒪[L] x) = IsLocalRing.residue 𝒪[L] x at hx
    rw [galoisGroupResidueFieldEquivOfIsIntegralClosure_residue K L σ x] at hx
    exact hx
  · intro h
    refine AlgEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    change galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ
        (IsLocalRing.residue 𝒪[L] x) = IsLocalRing.residue 𝒪[L] x
    rw [galoisGroupResidueFieldEquivOfIsIntegralClosure_residue K L σ x]
    exact h x

/-- The actual residue kernel consists exactly of automorphisms whose conjugate
differences lie in the maximal ideal. This proves the closed target for NYLL M160.018. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal :
    GaloisGroupResidueAlgEquivHomOfIsIntegralClosureMemKerIffSubMemMaximalIdealStatement.{u} := by
  intro K L _ _ _ _ _ _ _ σ
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_residue_eq K L σ]
  refine forall_congr' fun x => ?_
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]

end Langlands.NYLL.LocalFieldTheory
