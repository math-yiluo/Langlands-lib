/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.AbstractUnramified.DegreeStatement

/-!
# NYLL M330.006: finite abstract-field degree comparison

Adapted by Worker 203 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/AbstractUnramified.lean:190–230`.
Prove the published parameterized target, preserving its universe-zero field
and explicit normality binder. Replace the source's abstract index helper by
Mathlib's quotient-cardinality theorem and use the target's focused imports.
See the paired Markdown for the implemented proof and every modification;
the original license and notices remain in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation CyclicCohomology

noncomputable section

/-- The degree of a normal finite abstract field is the ordinary degree of
its concrete fixed field in the chosen separable closure. -/
theorem finiteAbstractField_degree_eq_abstractFixedField_finrank
    (K : Type) [Field K]
    (H : FiniteAbstractField
      (Gal(SeparableClosure K/K)))
    (hnormal :
      (extensionSubgroup
        (baseField (Gal(SeparableClosure K/K))) H.field
        (le_baseField H.field)).Normal) :
    finiteAbstractField_degree_eq_abstractFixedField_finrankStatement K H hnormal := by
  change (H.toFiniteAbstractExtension.degree : ℕ) =
    Module.finrank K (abstractFixedField K (SeparableClosure K) H.field)
  calc
    (H.toFiniteAbstractExtension.degree : ℕ) =
        (extensionSubgroup
          (baseField (Gal(SeparableClosure K/K))) H.field
          (le_baseField H.field)).index :=
      (Subgroup.index_eq_card _).symm
    _ = H.field.toSubgroup.index := by
      symm
      rw [← Subgroup.relIndex_top_right]
      rfl
    _ = (abstractFixedField K (SeparableClosure K) H.field).fixingSubgroup.index :=
      congrArg Subgroup.index (InfiniteGalois.fixingSubgroup_fixedField H.field).symm
    _ = Module.finrank K (abstractFixedField K (SeparableClosure K) H.field) :=
      (IntermediateField.finrank_eq_fixingSubgroup_index (SeparableClosure K) _).symm

end
end Langlands.NYLL.LocalClassFieldTheory
