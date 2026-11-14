/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only the proof of M086.020
normResidueNaturalityAbelianizedRestriction_of_mk from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Main.lean at
fbd320cd8b1b06487c58227e92eb135794267709, under the source name with the
Langlands.NYLL prefix, proving the published statement. Introduce the
statement's binders and keep the source tactic proof unchanged. The source
simp attribute is not installed.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main.U020.Statements

namespace Langlands.NYLL.ClassFormation

/-- Establishes the identity `normResidueNaturalityAbelianizedRestriction K K' L L' hLK hL'K' hK'K
hL'L (Abelianization.of (QuotientGroup.mk k')) = Abelianization.of (QuotientGroup.mk
(Subgroup.inclusion hK'K k'))`. -/
theorem normResidueNaturalityAbelianizedRestriction_of_mk.{u} :
    normResidueNaturalityAbelianizedRestriction_of_mkStatement.{u} := by
  intro G _ _ K K' L L' hLK hL'K' hK'K hL'L _ _ k'
  change
    (Abelianization.lift
      (Abelianization.of.comp
        (finiteReciprocityNaturalityRestriction K K' L L'
          hLK hL'K' hK'K hL'L)))
        (Abelianization.of (QuotientGroup.mk k')) = _
  rw [Abelianization.lift_apply_of]
  rfl

end Langlands.NYLL.ClassFormation
