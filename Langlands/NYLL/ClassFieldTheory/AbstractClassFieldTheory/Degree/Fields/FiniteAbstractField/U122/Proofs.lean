/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 395, 14 November 2026 UTC:
Extract only the proof of M010.122 (FiniteAbstractField.eq_of_field_eq)
from Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and import only the published FiniteAbstractField Statements module.
Omit the unused `open CyclicCohomology`, keep the noncomputable section,
`universe u`, the section variable line and the docstring, and state the
theorem as the published Statement applied to the source parameters. The
proof is unchanged. The original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Statements

/-!
# Extensionality of finite abstract fields

The proof that a finite abstract field is determined by its underlying
closed subgroup.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbstractField

/-- A finite abstract field is determined by its underlying closed subgroup;
the finiteness component is proof-irrelevant. -/
theorem eq_of_field_eq (K L : FiniteAbstractField G)
    (h : K.field = L.field) : eq_of_field_eqStatement K L h := by
  cases K with
  | mk K hK =>
    cases L with
    | mk L hL =>
      cases h
      rfl

end FiniteAbstractField

end
end Langlands.NYLL.ClassFormation
