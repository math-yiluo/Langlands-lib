/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 13 November 2026:
Prove the published closed statement
Langlands.NYLL.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_baseStatement
of M091.007 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
IntrinsicAbsoluteData.lean at fbd320cd8b1b06487c58227e92eb135794267709.
Add the Langlands.NYLL namespace prefix and import only the published
Base Statements module. Keep the first two source proof steps; replace the
final call of the unproved ClassFormation.FiniteAbstractField.eq_of_field_eq
(M010.122) by a local structure-extensionality argument. Drop the source
@[simp] attribute when giving the theorem the closed statement as its exact type. Omit all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.

Worker 691, 14 November 2026: prepare the shared Worker 57 proof for
submission, retaining its proof term and clarifying the paired documentation.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Base.Statements

/-!
# The finite intrinsic base is the distinguished finite base

The proof of the published closed proposition that, for every field `F`,
`intrinsicFiniteAbstractBase F` equals
`FiniteAbstractField.base (intrinsicAbsoluteGalois F)`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.ClassFormation

/-- The finite intrinsic base is the distinguished finite base of the
abstract class formation. -/
theorem intrinsicFiniteAbstractBase_eq_base :
    intrinsicFiniteAbstractBase_eq_baseStatement := by
  intro F _
  have h := closedFixingSubgroup_bot_eq_baseField F (SeparableClosure F)
  change intrinsicAbstractBase F =
    baseField (intrinsicAbsoluteGalois F) at h
  have key : ∀ K L : FiniteAbstractField (intrinsicAbsoluteGalois F),
      K.field = L.field → K = L := by
    rintro ⟨_, _⟩ ⟨_, _⟩ hKL
    cases hKL
    rfl
  exact key _ _ h

end Langlands.NYLL.LocalClassFieldTheory
