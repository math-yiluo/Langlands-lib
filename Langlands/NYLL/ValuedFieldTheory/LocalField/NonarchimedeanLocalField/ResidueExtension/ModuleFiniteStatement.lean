/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 252, 13 November 2026:
Extract M138.026, source lines 333–343, from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued definition.
Prefix the namespace with Langlands.NYLL and append Statement to the name;
preserve the universe, complete telescope and proposition. Omit the proof
and replace the original broad imports by the Mathlib dependencies below.
LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Mathlib.FieldTheory.Separable
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Valuation.Extension

/-!
# Finiteness of integer rings from integral closure: statement

The exact proposition target of NYLL M138.026.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Finite separable extensions whose valuation ring is the integral closure of
the base valuation ring give a finite module extension of valuation integer
rings. -/
def integerRing_moduleFinite_of_isIntegralClosureStatement (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] : Prop :=
  Module.Finite 𝒪[K] 𝒪[L]

end

end Langlands.NYLL.LocalFieldTheory
