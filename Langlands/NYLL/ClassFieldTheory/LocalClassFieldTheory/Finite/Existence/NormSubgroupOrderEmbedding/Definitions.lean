/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U001.Definitions

/-!
# Native finite abelian norm subgroup

Modified by Worker 536, 14 November 2026: extract M300.003 (lines 79–81,
with the docstring at lines 77–78) from NYLL's
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace
with `Langlands.NYLL`, replace the imports by the four published data modules
used here, and omit unused namespace openings and all other declarations.
The source telescope, docstring, definition kind and body are unchanged.
The paired Markdown records the source map and modifications.
See `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open LocalFieldTheory ClassFormation

variable (K : Type) [Field K]

/-- The actual norm subgroup of the fixed field represented by an abstract
finite abelian extension. -/
def finiteAbelianNormSubgroup
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) : Subgroup Kˣ :=
  localNormSubgroup K (abstractFixedField K (SeparableClosure K) L.field)

end Langlands.NYLL.LocalClassFieldTheory
