/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 323 on 13 November 2026: extract only the signatures of
M289.003–004 from Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/
StandardOpenSubgroups.lean at fbd320cd8b1b06487c58227e92eb135794267709.
Replace theorems with Prop-valued definitions bearing the Statement suffix,
prefix the namespace with Langlands.NYLL, and use focused published imports.
The original universes, parameters, hypotheses and conclusions are retained.
See Statements.md and licenses/NYLL/ for correspondence and attribution.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups.Definitions
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Targets for principal units inside neighborhoods and open subgroups

These two propositions retain the positive filtration index of the source.
-/

noncomputable section

namespace Langlands.NYLL.LocalFieldTheory

open scoped ValuativeRel

open Filter

universe u

/-- Every neighborhood of one contains a positive principal-unit group. -/
def exists_fieldPrincipalUnits_subset_of_mem_nhdsStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (U : Set Kˣ) (hU : U ∈ nhds (1 : Kˣ)) : Prop :=
  ∃ n : Nat, 1 ≤ n ∧ (fieldPrincipalUnits K n : Set Kˣ) ⊆ U

/-- Every open subgroup of the multiplicative group of a nonarchimedean local
field contains a sufficiently deep positive principal-unit group. -/
def exists_fieldPrincipalUnits_le_of_isOpenStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : Subgroup Kˣ) (hH : IsOpen (H : Set Kˣ)) : Prop :=
  ∃ n : Nat, 1 ≤ n ∧ fieldPrincipalUnits K n ≤ H

end Langlands.NYLL.LocalFieldTheory
