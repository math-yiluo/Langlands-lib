/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 3, 2026-11-13: state only M264.016, the theorem
isCyclic_galoisGroup_of_unramifiedValuation at lines 400–412 of
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709, as the closed
proposition isCyclic_galoisGroup_of_unramifiedValuationStatement in the
namespace prefixed with Langlands.NYLL; omit the source proof; replace the
source imports by the published module defining the unramified class and two
Mathlib modules. The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.Definitions
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# The Galois group of a finite unramified extension is cyclic: target

This module states only M264.016, lines 400–412 of
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean`.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- Target for NYLL M264.016: the Galois group of a finite Galois unramified
extension of nonarchimedean local fields is cyclic. -/
def isCyclic_galoisGroup_of_unramifiedValuationStatement : Prop :=
  ∀ (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L],
    IsCyclic Gal(L / K)

end Langlands.NYLL.LocalFieldTheory
