/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 177, 12 November 2026:
Extract only M129.004 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Norm.lean at
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL, omit the unused section variables and all other
declarations, and retain the source universes, telescope and body.
Replace the source imports by the two Mathlib modules the definition needs.
See paired Markdown.
The upstream LICENSE and NOTICE are preserved in licenses/NYLL/.
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Field.Defs

/-!
# Base-field units embedded in extension-field units

The algebra map of a field extension, applied to unit groups.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u v

namespace IsNonarchimedeanLocalField

/-- Base units embedded in an extension. -/
def mapBaseUnitsToExtensionUnits
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    Kˣ →* Lˣ :=
  Units.map (algebraMap K L).toMonoidHom

end IsNonarchimedeanLocalField

end

end Langlands.NYLL.LocalFieldTheory
