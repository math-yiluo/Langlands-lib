/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Galois ambient units and intermediate-field unit inclusion

Adapted from Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean`,
lines 33–45 (M088.001–002).

Modifications by Worker 169: extract the two initial data declarations; prefix
`LocalClassFieldTheory` with `Langlands.NYLL`; replace the two NYLL imports by
focused Mathlib imports; remove unused namespace openings and narrow the module
documentation. The source parameters, docstrings and literal bodies are unchanged.
See the paired Markdown for the complete declaration and modification map.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]

/-- The actual Galois representation on `Ωˣ`, written additively for the
group-cohomology API. -/
abbrev galoisAmbientUnitsRep : Rep ℤ (Gal(Ω / K)) :=
  Rep.ofAlgebraAutOnUnits K Ω

/-- Inclusion of the units of an intermediate field into the units of the
chosen Galois ambient field, in additive notation. -/
def intermediateFieldUnitsToGaloisAmbient
    (E : IntermediateField K Ω) :
    Additive Eˣ →+ Additive Ωˣ :=
  MonoidHom.toAdditive (Units.map E.val.toRingHom)

end
end Langlands.NYLL.LocalClassFieldTheory
