/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Compositum
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions

/-!
# The fixed field of an abstract compositum: proposition target

Modified by Worker 451, 14 November 2026: extract the type of M300.005
(lines 128–132) of the pinned NYLL
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`. The source theorem becomes a
Prop-valued definition with the suffix `Statement`; the source section
variables `(K : Type) [Field K]` are written as its leading explicit binders,
and the proof is omitted. The namespace is prefixed with `Langlands.NYLL`, the
source imports are replaced by the published modules supplying the used
declarations, and the unused source openings are dropped. See the paired
Markdown for the declaration map and complete modification record. The
original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

/-- The concrete fixed field of an abstract compositum is the compositum of
the two concrete fixed fields inside the chosen separable closure. -/
def finiteAbelianSubextension_compositum_fixedFieldStatement
    (K : Type) [Field K]
    (U T : FiniteAbelianSubextension (intrinsicAbstractBase K)) : Prop :=
  abstractFixedField K (SeparableClosure K) (U.compositum T).field =
    abstractFixedField K (SeparableClosure K) U.field ⊔
      abstractFixedField K (SeparableClosure K) T.field

end Langlands.NYLL.LocalClassFieldTheory
