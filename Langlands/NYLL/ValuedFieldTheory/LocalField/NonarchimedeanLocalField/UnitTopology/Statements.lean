/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 94, 12 November 2026: extract the statements of
M256.002–003 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnitTopology.lean
at fbd320cd8b1b06487c58227e92eb135794267709; add Langlands.NYLL to the
namespace and Statement to both names. Replace the theorem proofs by
Prop-valued definitions, and import the published subgroup's focused module.
Preserve every source universe, parameter, instance and proposition.
LICENSE and NOTICE: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnitTopology.U001.Definitions

/-!
# Targets for the valuation-integer unit subgroup

These two proposition definitions record the source valuation characterization
and openness targets for the published subgroup.
-/

noncomputable section

universe u

namespace Langlands.NYLL.LocalFieldTheory

open scoped ValuativeRel

/-- Target: a field unit lies in the image of valuation-ring units exactly when
its valuation is one. -/
def mem_localBaseUnitSubgroup_iff_valuation_eq_oneStatement
    (K : Type u) [Field K] [ValuativeRel K] (x : Kˣ) : Prop :=
  x ∈ localBaseUnitSubgroup K ↔ ValuativeRel.valuation K (x : K) = 1

/-- Target: the image of valuation-ring units is open in the native topology of
a nonarchimedean local field. -/
def localBaseUnitSubgroup_isOpenStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Prop :=
  IsOpen (localBaseUnitSubgroup K : Set Kˣ)

end Langlands.NYLL.LocalFieldTheory
