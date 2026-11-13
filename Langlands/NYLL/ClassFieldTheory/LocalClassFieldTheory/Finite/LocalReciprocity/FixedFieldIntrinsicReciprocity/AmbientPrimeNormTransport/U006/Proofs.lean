/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only the proof of M283.006 normUnits_mapEquiv from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and import only the published U006 Statements module. Prove the
closed proposition by introducing its binders and then retaining the
original tactic proof. Omit the original noncomputable section, the
namespace openings and all other declarations of the module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U006.Statements

/-!
# Unit norms under compatible field equivalences: proof

The proof of the published closed proposition that unit norms are
transported by a pair of ring equivalences of the base and extension fields
that commute with the algebra maps.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Field norms on units commute with compatible ring equivalences of the
base and extension fields. -/
theorem normUnits_mapEquiv : normUnits_mapEquivStatement := by
  intro F E F₀ E₀ _ _ _ _ _ _ phiF phiE hcomm y
  apply Units.ext
  change
    Algebra.norm F₀ (phiE (y : E)) =
      phiF (Algebra.norm F (y : E))
  have hnorm :=
    Algebra.norm_eq_of_equiv_equiv
      phiF phiE hcomm (y : E)
  apply phiF.symm.injective
  rw [phiF.symm_apply_apply]
  exact hnorm.symm

end Langlands.NYLL.LocalClassFieldTheory
