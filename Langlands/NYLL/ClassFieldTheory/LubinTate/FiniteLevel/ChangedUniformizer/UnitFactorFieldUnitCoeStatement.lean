/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 328, 2026-11-14: extract only the proposition of
M391.008 from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
add the Langlands.NYLL namespace prefix and Statement suffix, close the
source telescope with universal quantifiers, and use the focused published
M391.007 import. Omit the theorem proof, simp attribute and noncomputable
section. See the paired Markdown for the complete adaptation record.
The retained license and notice are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer.UnitFactorFieldUnit

/-!
# Unit-factor coercion target

The exact proposition of NYLL M391.008, using the published unit-factor
field unit. The paired Markdown records the source and adaptations.
-/

universe u v

namespace Langlands.NYLL.LubinTate

/-- The statement that the unit-factor inclusion has the expected underlying
field element. -/
def standardLubinTateUnitFactorFieldUnit_coeStatement : Prop :=
  ∀ {K : Type u} [Field K]
    (F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K)
    (u : F.valuationSubringˣ),
    (standardLubinTateUnitFactorFieldUnit F u : K) =
      (u : F.valuationSubring)

end Langlands.NYLL.LubinTate
