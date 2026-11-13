/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 13 November 2026:
Extract the statement of M270.009 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionTopology.lean
at fbd320cd8b1b06487c58227e92eb135794267709 as a closed Prop-valued definition
without its proof. Add the Langlands.NYLL namespace prefix and the suffix
Statement. Replace the source's own spectral norm and valuative relation
(M270.003 finiteExtensionSpectralNormedField and M270.007
finiteExtensionSpectralValuativeRel) by the Library's
Langlands.LocalField.FiniteExtension.normedField and
Langlands.LocalField.FiniteExtension.valuativeRel, and import their Library
module instead of the source imports. Omit all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.LocalField.FiniteExtension

/-!
# The spectral valuation extends the base valuation: statement

The closed proposition that, on a finite extension of a nonarchimedean local
field, the valuation of the spectral valuative relation extends the canonical
valuation of the base field.
-/

namespace Langlands.NYLL.LocalFieldTheory

/-- The valuative relation coming from the spectral norm is the canonical
extension of the native valuation on the local base field. -/
def finiteExtensionSpectralValuation_hasExtensionStatement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    letI : NontriviallyNormedField L :=
      Langlands.LocalField.FiniteExtension.normedField K L
    letI : ValuativeRel L := Langlands.LocalField.FiniteExtension.valuativeRel K L
    Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)

end Langlands.NYLL.LocalFieldTheory
