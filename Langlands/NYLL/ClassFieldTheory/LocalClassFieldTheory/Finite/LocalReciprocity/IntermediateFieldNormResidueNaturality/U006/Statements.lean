/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 30, 13 November 2026: extracted the private source theorem
LocalClassFieldTheory.commGroup_abelianizationCongr_of (inventory M260.006) as the
public Prop-valued target Langlands.NYLL.PortInternal.M260.d006Statement.
The source proof is omitted. The theorem's own telescope is unchanged; the
enclosing section's local-field variables are not mentioned by the source statement
and so are not parameters of the source theorem either. The imports are reduced to
Mathlib.GroupTheory.Abelianization.Defs.
The retained license and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Abelianization of an isomorphism onto a commutative group: statement target

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/IntermediateFieldNormResidueNaturality.lean`,
lines 140–145 (inventory M260.006).
-/

noncomputable section

namespace Langlands.NYLL.PortInternal.M260

/-- For an isomorphism `q : G ≃* H` onto a commutative group, the abelianized
isomorphism followed by the inverse of `Abelianization.equivOfComm` sends the class
of `x` to `q x`. -/
def d006Statement
    {G H : Type*} [Group G] [CommGroup H]
    (q : G ≃* H) (x : G) : Prop :=
  (Abelianization.equivOfComm (H := H)).symm
      (q.abelianizationCongr (Abelianization.of x)) =
    q x

end Langlands.NYLL.PortInternal.M260
