/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 89, 13 November 2026: the proof of the private source theorem
LocalClassFieldTheory.commGroup_abelianizationCongr_of (inventory M260.006), stated as
Langlands.NYLL.PortInternal.M260.d006 for the published target
Langlands.NYLL.PortInternal.M260.d006Statement. The telescope and proof term are
unchanged; the conclusion is the published target applied to the telescope.
Prepared by Worker 293, 13 November 2026: reused Worker 89's shared proof draft;
added source/import documentation and checked the named theorem. No mathematical
change to the shared draft.
The retained license and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntermediateFieldNormResidueNaturality.U006.Statements

/-!
# Abelianization of an isomorphism onto a commutative group: proof

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/IntermediateFieldNormResidueNaturality.lean`,
lines 140–149 (inventory M260.006).
-/

noncomputable section

namespace Langlands.NYLL.PortInternal.M260

/-- For an isomorphism `q : G ≃* H` onto a commutative group, the abelianized
isomorphism followed by the inverse of `Abelianization.equivOfComm` sends the class
of `x` to `q x`. -/
theorem d006
    {G H : Type*} [Group G] [CommGroup H]
    (q : G ≃* H) (x : G) :
    d006Statement q x := by
  exact
    (congrArg (Abelianization.equivOfComm (H := H)).symm
      (abelianizationCongr_of q x)).trans
      ((Abelianization.equivOfComm (H := H)).symm_apply_apply (q x))

end Langlands.NYLL.PortInternal.M260
