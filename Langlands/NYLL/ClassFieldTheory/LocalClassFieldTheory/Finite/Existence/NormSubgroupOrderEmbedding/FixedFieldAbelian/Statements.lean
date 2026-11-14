/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Abelian
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions

/-!
# The fixed field of a finite abelian subextension is abelian: proposition target

Modified by Worker 451, 14 November 2026: extract the type of M300.004
(lines 87–90) of the pinned NYLL
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`. The source theorem becomes a
Prop-valued definition with the suffix `Statement`; the source section
variables `(K : Type) [Field K]` are written as its leading explicit binders,
and the proof is omitted. The namespace is prefixed with `Langlands.NYLL`, the
source imports are replaced by the published modules supplying the used
declarations together with Mathlib's `FieldTheory.Galois.Abelian`, and the
unused source openings are dropped. See the paired Markdown for the
declaration map and complete modification record. The original license and
notices are retained in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

/-- The fixed field represented by an abstract finite abelian extension is
an actual finite abelian extension of `K`.  The commutativity assertion is
transported across the concrete quotient--Galois-group equivalence, rather
than being inferred merely from the name of the abstract package. -/
def finiteAbelianSubextension_fixedField_isAbelianGaloisStatement
    (K : Type) [Field K]
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) : Prop :=
  IsAbelianGalois K
    (abstractFixedField K (SeparableClosure K) L.field)

end Langlands.NYLL.LocalClassFieldTheory
