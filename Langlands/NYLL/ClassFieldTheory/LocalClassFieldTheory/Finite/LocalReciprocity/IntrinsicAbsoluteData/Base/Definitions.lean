/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions

/-!
# The intrinsic abstract base as a finite abstract field

Adapted by Worker 57 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory
open ClassFormation

/-- The intrinsic abstract base packaged as a finite abstract field; its
defining quotient is the trivial finite quotient. -/
@[reducible]
noncomputable def intrinsicFiniteAbstractBase
    (F : Type) [Field F] :
    FiniteAbstractField (intrinsicAbsoluteGalois F) where
  field := intrinsicAbstractBase F
  finite := by
    rw [intrinsicAbstractBase, closedFixingSubgroup_bot_eq_baseField]
    exact (FiniteAbstractField.base (intrinsicAbsoluteGalois F)).finite

end Langlands.NYLL.LocalClassFieldTheory
