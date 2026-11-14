/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.LocalField.Basic
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.Initial.Definitions

/-!
# The local multiplicative group satisfies the class-field axiom: target

Adapted by Worker 90 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalClassFieldAxiom.lean`,
lines 144–152 (M159.002).

Modifications by Worker 90: the source theorem becomes the Prop-valued
`Statement` definition below whose body is the source conclusion, with the
source binders unchanged; prefix the namespace `LocalClassFieldTheory` with
`Langlands.NYLL`; replace the source imports by the published modules
providing `SatisfiesClassFieldAxiom` and `galoisAmbientUnitsRep` and the
Mathlib modules providing `SeparableClosure` and
`IsNonarchimedeanLocalField`; omit the proof and the private source theorem
M159.001 it applies. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

/-- Target for M159.002: the coefficient module `A = (kˢᵉᵖ)ˣ` satisfies the
abstract class-field axiom.  This is the separable-closure specialization used
for local reciprocity. -/
def separableClosureUnits_isClassFormationStatement
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : Prop :=
  SatisfiesClassFieldAxiom
    (galoisAmbientUnitsRep k (SeparableClosure k))

end Langlands.NYLL.LocalClassFieldTheory
