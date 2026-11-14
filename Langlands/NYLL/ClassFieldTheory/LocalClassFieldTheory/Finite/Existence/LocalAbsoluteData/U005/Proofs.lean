/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.LocalAbsoluteData.U005.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.U002.Proofs

/-!
# NYLL M299.005: base normality makes the abstract fixed field Galois

Adapted by Worker 664 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, M299.005, lines 67–103.
The theorem retains the complete source telescope and proves the published
Prop target. The source membership-lemma step is replaced by reflexivity
for the published `extensionSubgroup` abbreviation. See the paired Markdown
and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open CyclicCohomology ClassFormation

/-- Normality over the abstract base fixing group makes the represented
fixed field Galois over the concrete local base field. -/
theorem abstractFixedField_isGalois_of_base_normal
    (K : Type) [Field K]
    (H : ClosedSubgroup (Gal(SeparableClosure K/K)))
    (hnormal :
      (extensionSubgroup
        (baseField (Gal(SeparableClosure K/K))) H
        (le_baseField H)).Normal) :
    abstractFixedField_isGalois_of_base_normalStatement K H hnormal := by
  let B := baseField (Gal(SeparableClosure K / K))
  have hsub :
      extensionSubgroup B H (le_baseField H) =
        H.toSubgroup.subgroupOf B.toSubgroup := by
    rfl
  have hrelative :
      (H.toSubgroup.subgroupOf B.toSubgroup).Normal := by
    rw [← hsub]
    exact hnormal
  have hconj :
      ∀ h g : Gal(SeparableClosure K / K),
        h ∈ H.toSubgroup → g ∈ B.toSubgroup →
          g * h * g⁻¹ ∈ H.toSubgroup :=
    (Subgroup.normal_subgroupOf_iff (le_baseField H)).1 hrelative
  let : H.toSubgroup.Normal :=
    { conj_mem := fun h hh g => hconj h g hh (by simp [B, baseField]) }
  apply (InfiniteGalois.normal_iff_isGalois
    (abstractFixedField K (SeparableClosure K) H)).1
  have hfix :
      (abstractFixedField K (SeparableClosure K) H).fixingSubgroup =
        H.toSubgroup := by
    have hclosed := closedFixingSubgroup_abstractFixedField_eq
      K (SeparableClosure K) H
    exact congrArg ClosedSubgroup.toSubgroup hclosed
  rw [hfix]
  infer_instance

end Langlands.NYLL.LocalClassFieldTheory
