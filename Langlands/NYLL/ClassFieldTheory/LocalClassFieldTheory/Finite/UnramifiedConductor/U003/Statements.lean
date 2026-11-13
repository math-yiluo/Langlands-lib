/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 330, 13 November 2026:
Extract only the proposition of M372.003 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/UnramifiedConductor.lean
at fbd320cd8b1b06487c58227e92eb135794267709, lines 115–122.
Add the Langlands.NYLL namespace prefix and the Statement suffix; replace
the theorem with a Prop-valued definition, preserving its full telescope.
Erase the unused result-type letI : Finite (NormQuotient K L), as checked
by the focused compatibility example recorded in the paired Markdown.
Reuse the published actual NormQuotient with focused Mathlib imports.
No proof or Finite instance is extracted. The original LICENSE and NOTICE
are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U002.Definitions
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Abelian norm-quotient index target

The order of the actual norm quotient equals the finite abelian extension degree.
See the paired Markdown for source correspondence and the letI modification.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

/-- The norm quotient in a finite abelian extension has order equal to the field degree. -/
def card_normQuotient_eq_finrank_of_isAbelianGaloisStatement
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] : Prop :=
  Nat.card (Langlands.NYLL.LocalFieldTheory.NormQuotient K L) = Module.finrank K L

end

end Langlands.NYLL.LocalClassFieldTheory
