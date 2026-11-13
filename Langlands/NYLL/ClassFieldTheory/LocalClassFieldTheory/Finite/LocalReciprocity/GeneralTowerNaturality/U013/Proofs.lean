/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 89, 13 November 2026: the proof of the source theorem
LocalClassFieldTheory.restrictNormalHom_eq_autCongr (inventory M262.013), stated as
Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_eq_autCongr for the published
target restrictNormalHom_eq_autCongrStatement. The telescope and tactic proof are
unchanged; the conclusion is the published target applied to the telescope.
Verified by Worker 295, 13 November 2026: retained Worker 89's proof draft,
compared its telescope and tactic proof with the pinned original, and expanded
the paired documentation of imports and attribution.
The retained license and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality.U013.Statements

/-!
# Restriction along an algebra equivalence is conjugation: proof

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GeneralTowerNaturality.lean`,
lines 402–436 (inventory M262.013).
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

/-- When `L` is regarded as an `M`-algebra through the inverse of a
`K`-algebra equivalence, restriction from `L` to `M` is conjugation by that
equivalence. -/
theorem restrictNormalHom_eq_autCongr
    (K L M : Type)
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [Normal K M]
    (e : L ≃ₐ[K] M) :
    restrictNormalHom_eq_autCongrStatement K L M e := by
  let : Algebra M L := e.symm.toRingHom.toAlgebra
  let : IsScalarTower K M L :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (e.symm.commutes x).symm)
  apply MonoidHom.ext
  intro sigma
  apply AlgEquiv.ext
  intro x
  apply e.symm.injective
  calc
    e.symm ((AlgEquiv.restrictNormalHom M sigma) x) =
        sigma (e.symm x) := by
      exact AlgEquiv.restrictNormal_commutes sigma M x
    _ = e.symm ((AlgEquiv.autCongr e sigma) x) := by
      simp [AlgEquiv.autCongr_apply]

end Langlands.NYLL.LocalClassFieldTheory
