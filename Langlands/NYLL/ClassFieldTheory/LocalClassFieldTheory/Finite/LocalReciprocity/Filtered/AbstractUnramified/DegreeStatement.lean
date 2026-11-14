/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsSepClosed

/-!
# NYLL M330.006: finite abstract-field degree comparison target

Adapted by Worker 291 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/AbstractUnramified.lean:192–230`.
Prefix the namespace, replace the source theorem by a Prop-valued definition,
reduce its fixed-field abbreviation and two unused local instance bindings,
and use focused published imports. Retain the source binders, including
`K : Type` and `hnormal`. The proof is omitted.
See the paired Markdown for the exact correspondence and modification record;
the original license and notices are in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation CyclicCohomology

noncomputable section

/-- Target: the degree of a normal finite abstract field is the ordinary
degree of its concrete fixed field in the chosen separable closure. -/
def finiteAbstractField_degree_eq_abstractFixedField_finrankStatement
    (K : Type) [Field K]
    (H : FiniteAbstractField
      (Gal(SeparableClosure K/K)))
    (hnormal :
      (extensionSubgroup
        (baseField (Gal(SeparableClosure K/K))) H.field
        (le_baseField H.field)).Normal) : Prop :=
  (H.toFiniteAbstractExtension.degree : ℕ) =
    Module.finrank K (abstractFixedField K (SeparableClosure K) H.field)

end
end Langlands.NYLL.LocalClassFieldTheory
