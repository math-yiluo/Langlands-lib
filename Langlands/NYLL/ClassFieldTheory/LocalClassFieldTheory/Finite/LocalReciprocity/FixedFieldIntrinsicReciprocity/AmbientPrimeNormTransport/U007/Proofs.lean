/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026, and Worker 520, 14 November 2026:
Extract only M283.007 normClass_mapEquiv from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and prove the published closed proposition by introducing its binders.
Worker 56 prepared the shared draft with the sibling normUnits_mapEquiv proof
inlined. Worker 520 reuses the now-published sibling proof, restoring the
original tactic proof after the binder introductions. Import the published
U006 Statements and Proofs modules and the published proof of
Langlands.NYLL.LocalFieldTheory.normClass_eq_iff_exists_norm_div.
Omit the original noncomputable section, unused namespace openings and all
other declarations. The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U006.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U006.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U031.Proofs

/-!
# Norm classes under compatible field equivalences: proof

Equality of unit norm classes is transported by ring equivalences of the
base and extension fields that commute with the algebra maps.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory

/-- Compatible ring equivalences preserve equality of unit norm classes. -/
theorem normClass_mapEquiv : normClass_mapEquivStatement := by
  intro F E F₀ E₀ _ _ _ _ _ _ phiF phiE hcomm a x h
  rw [normClass_eq_iff_exists_norm_div] at h ⊢
  rcases h with ⟨y, hy⟩
  refine ⟨Units.mapEquiv phiE.toMulEquiv y, ?_⟩
  have hnorm :=
    normUnits_mapEquiv F E F₀ E₀ phiF phiE hcomm y
  rw [← map_div, hy]
  exact hnorm.symm

end Langlands.NYLL.LocalClassFieldTheory
