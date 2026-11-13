/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.IsSepClosed
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.Initial.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions

/-!
# Intrinsic absolute Galois group, units and base

Adapted by Worker 203 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

noncomputable section
namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory
/-- The absolute Galois group of a field, formed using its chosen separable closure. -/
abbrev intrinsicAbsoluteGalois
    (F : Type) [Field F] :=
  Gal(SeparableClosure F / F)

/-- The integral representation of the intrinsic absolute Galois group on the
units of the chosen separable closure. -/
abbrev intrinsicAbsoluteUnits
    (F : Type) [Field F] :
    Rep ℤ (intrinsicAbsoluteGalois F) :=
  galoisAmbientUnitsRep F (SeparableClosure F)

/-- The closed base subgroup of the intrinsic absolute Galois group, expressed
as the fixing subgroup of the bottom intermediate field. -/
abbrev intrinsicAbstractBase
    (F : Type) [Field F] :
    ClosedSubgroup (intrinsicAbsoluteGalois F) :=
  closedFixingSubgroup F (SeparableClosure F)
    (⊥ : IntermediateField F (SeparableClosure F))
end Langlands.NYLL.LocalClassFieldTheory
