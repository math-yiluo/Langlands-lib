/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.U006.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.U009.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldNorm.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnitsEquiv.U007.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Initial.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.U002.Proofs

/-!
# Abstract fixed-field relative norm: value equality

Modified by Worker 537, 16 November 2026: extract the proof of M300.006
from `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace
with `Langlands.NYLL`, make the source section parameters explicit, and
state the conclusion as the published `Statement` applied to the complete
source telescope. Unfold that target before the unchanged source tactic
proof. Replace the broad upstream imports with focused published modules
and omit unrelated declarations and unused namespace openings.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory CyclicCohomology KummerTheory ClassFormation

/-- The relative class-formation norm of an abstract fixed-field unit has
the same ambient field value as its ordinary field norm. -/
theorem relativeNorm_abstractFixedFieldUnit_val_of_isGalois
    (K : Type) [Field K]
    (H : ClosedSubgroup (intrinsicAbsoluteGalois K))
    (hH : H.toSubgroup ≤ (intrinsicAbstractBase K).toSubgroup)
    [Finite ((intrinsicAbstractBase K).toSubgroup ⧸
      extensionSubgroup (intrinsicAbstractBase K) H hH)]
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H)]
    [IsGalois K (abstractFixedField K (SeparableClosure K) H)]
    (x : (abstractFixedField K (SeparableClosure K) H)ˣ) :
    relativeNorm_abstractFixedFieldUnit_val_of_isGaloisStatement K H hH x := by
  unfold relativeNorm_abstractFixedFieldUnit_val_of_isGaloisStatement
  let E := abstractFixedField K (SeparableClosure K) H
  let y : ambientFixedAddSubgroup (intrinsicAbsoluteUnits K) H :=
    abstractFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H (Additive.ofMul x)
  let yE := intermediateFieldUnitsEquivGaloisFixed
    K (SeparableClosure K) E (Additive.ofMul x)
  have hy : yE.1 = y.1 := by
    rw [intermediateFieldUnitsEquivGaloisFixed_coe]
    exact (abstractFixedFieldUnitsEquivGaloisFixed_coe
      K (SeparableClosure K) H (Additive.ofMul x)).symm
  have hnorm :=
    relativeNorm_intermediateFieldUnit_val_of_isSeparable
      K (SeparableClosure K) E x
  have htransport := relativeNorm_coe_eq_of_closedSubgroup_eq
    (intrinsicAbsoluteUnits K)
    (intrinsicAbstractBase K) (intrinsicAbstractBase K)
    (closedFixingSubgroup K (SeparableClosure K) E) H
    (fixingSubgroupLeBase K (SeparableClosure K) E) hH
    rfl (closedFixingSubgroup_abstractFixedField_eq
      K (SeparableClosure K) H)
    yE y hy
  have htransport' := congrArg
    (fun z : Additive (SeparableClosure K)ˣ ↦
      ((Additive.toMul z : (SeparableClosure K)ˣ) : SeparableClosure K))
    htransport
  change
    ((Additive.toMul
      ((relativeNorm (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K)
        H hH y).1 : Additive (SeparableClosure K)ˣ) :
        (SeparableClosure K)ˣ) : SeparableClosure K) = _
  exact htransport'.symm.trans hnorm

end Langlands.NYLL.LocalClassFieldTheory
