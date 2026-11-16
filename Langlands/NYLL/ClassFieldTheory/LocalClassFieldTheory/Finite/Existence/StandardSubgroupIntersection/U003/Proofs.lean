/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 548, 16 November 2026: extract the proof of M403.003,
StandardSubgroupIntersection.lean lines 155–175, from commit
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
Langlands.NYLL and prove the published closed proposition by unfolding it
and introducing its complete source telescope. Replace broad source imports
with the published target and its two proof prerequisites. See the paired
Markdown for the proof and modifications. The original LICENSE and NOTICE
remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardSubgroupIntersection.U003.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardSubgroupIntersection.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.NormSubgroup.U032.Proofs

/-!
# Finite abelian compositum standard norm containment: proof

Source: M403.003, lines 135–175 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/StandardSubgroupIntersection.lean`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- The same standard-subgroup containment while retaining both inputs and
their compositum as finite abelian subextensions. -/
theorem finiteAbelianCompositum_normSubgroup_le_of_standard :
    finiteAbelianCompositum_normSubgroup_le_of_standardStatement := by
  unfold finiteAbelianCompositum_normSubgroup_le_of_standardStatement
  intro K _ _ _ _ H ϖ d n hϖ hstandard U T hUle hTle
  let A := intrinsicAbsoluteUnits K
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  intro x hx
  have hxUT :
      x ∈ U.normSubgroup A ⊓ T.normSubgroup A :=
    ClassFormation.FiniteAbelianSubextension.normSubgroup_compositum_le_inf
      A U T hx
  have hxUnramAdd : e.symm x ∈
      (unramifiedNormSubgroup K d).toAddSubgroup :=
    hUle ⟨x, hxUT.1, rfl⟩
  have hxPrincipalAdd : e.symm x ∈
      (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n).toAddSubgroup :=
    hTle ⟨x, hxUT.2, rfl⟩
  have hxStandard : Additive.toMul (e.symm x) ∈
      LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n :=
    unramifiedNormSubgroup_inf_uniformizerPrincipalSubgroup_le
      K ϖ d n hϖ ⟨hxUnramAdd, hxPrincipalAdd⟩
  have hxH : e.symm x ∈ H.toAddSubgroup := by
    change Additive.toMul (e.symm x) ∈ H
    exact hstandard hxStandard
  exact ⟨e.symm x, hxH, e.apply_symm_apply x⟩

end Langlands.NYLL.LocalClassFieldTheory
