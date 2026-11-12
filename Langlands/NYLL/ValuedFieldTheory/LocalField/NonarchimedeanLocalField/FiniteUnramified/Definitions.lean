/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 8, 2026-11-08: extract only M161.001, the class
IsUnramifiedValuedExtension at lines 32–44 of upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL; let the two fields have independent universes u and v instead
of the single source universe u; replace the source imports by four Mathlib
modules. The parameters and the class field are otherwise unchanged. The
retained license and notices are in licenses/NYLL/.
-/

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
# Finite unramified valued extensions: the class

This module adapts only M161.001, lines 32–44 of
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean`.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel

/-- A finite valuation extension is unramified at the actual valuation-ring
frontier when the ramification index of the maximal ideals is one.

This is the concrete source needed for residue-field automorphism comparisons. -/
class IsUnramifiedValuedExtension (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] : Prop where
  /-- The maximal ideal of `𝒪[L]` has ramification index one over `𝒪[K]`. -/
  maximalIdeal_ramificationIdx_eq_one :
    (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] = 1

end IsNonarchimedeanLocalField

end Langlands.NYLL.LocalFieldTheory
