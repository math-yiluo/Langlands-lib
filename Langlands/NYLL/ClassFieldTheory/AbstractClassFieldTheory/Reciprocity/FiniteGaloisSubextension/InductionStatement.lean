/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions

/-!
# NYLL M040.016: finite Galois quotient induction target

Modified by Worker 529: extract the protected theorem at lines 158–166 of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`
as a Prop-valued definition with suffix `Statement`, preserving its telescope
and conclusion under `Langlands.NYLL`. Replace the source import with the
published definitions module. The paired Markdown records every modification.
See `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

set_option linter.unusedVariables false in
/-- Target M040.016: eliminate a finite Galois quotient without exposing a
chosen representative. -/
protected def extensionQuotient_inductionOnStatement
    (L : FiniteGaloisSubextension K) {motive : L.extensionQuotient → Prop}
    (q : L.extensionQuotient)
    (mk : ∀ k : K.toSubgroup, motive (L.extensionQuotientMk k)) : Prop :=
  motive q

end FiniteGaloisSubextension

end Langlands.NYLL.ClassFormation
