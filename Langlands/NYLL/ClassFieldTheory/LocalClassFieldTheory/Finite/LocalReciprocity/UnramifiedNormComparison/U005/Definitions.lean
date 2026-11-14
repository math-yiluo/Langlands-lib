/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 205, 2026-11-14: extract M267.005, lines 94–101 of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean
at commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace
with Langlands.NYLL; replace the source cyclicity theorem by transport from
the published residue Galois equivalence and Mathlib's finite-field cyclicity,
following Worker 3's shared M264.016 proof draft. Retain the source Type-0
telescope, local instances and Abelianization.equivOfComm construction.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.ResidueEquivDefinitions
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# The unramified Galois group and its abelianization

NYLL source unit M267.005, with cyclicity obtained from the residue extension.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K L : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K)
    (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]
  [Module.Finite 𝒪[K] 𝒪[L]]
  [IsUnramifiedValuedExtension K L]

/-- Cyclicity identifies the unramified Galois group with its abelianization. -/
noncomputable def galoisGroupEquivAbelianizationOfUnramifiedValuation :
    Gal(L / K) ≃* Abelianization (Gal(L / K)) := by
  letI : IsCyclic (Gal(L / K)) :=
    (galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L).isCyclic.mpr
      inferInstance
  letI : CommGroup (Gal(L / K)) :=
    IsCyclic.commGroup (α := Gal(L / K))
  exact Abelianization.equivOfComm (H := Gal(L / K))

end Langlands.NYLL.LocalClassFieldTheory
