/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 785 (2026-10-30): extract only M248.001 from
   upstream commit fbd320cd8b1b06487c58227e92eb135794267709, prefix the
   namespace with Langlands.NYLL, replace the original imports by
   Mathlib.NumberTheory.LocalField.Basic and the published M247.004
   constructor module, take cyclicity of the value group from the current
   Mathlib instance instead of transporting it along the order isomorphism
   with `ℤᵐ⁰`, spell the value group as `valueGroup (.ofClass v)` as current
   Mathlib's `Valuation.IsRankOneDiscrete.mk'` requires, and bind `v` with
   `letI` so that it is inlined. The original LICENSE and NOTICE are retained
   in licenses/NYLL/. -/

import Mathlib.NumberTheory.LocalField.Basic
import Langlands.NYLL.ValuedFieldTheory.Valuation.ValuedAdicComplete.CompleteDVF

/-!
# The canonical complete discrete valuation of a nonarchimedean local field

The canonical valuation of a nonarchimedean local field, packaged as a
`CompleteDVF` through a uniformity compatible with the given topology.
-/

noncomputable section

namespace Langlands.NYLL.LocalFieldTheory

open ValuationTheory.DiscreteValuationField

universe u

/-- The canonical valuation of a nonarchimedean local field, packaged as a
complete discrete valuation field. -/
noncomputable def localCompleteDVF
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    CompleteDVF.{u, u} K := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI v : _root_.Valuation K (ValuativeRel.ValueGroupWithZero K) := Valued.v
  letI : v.IsNontrivial :=
    (ValuativeRel.isNontrivial_iff_isNontrivial v).mp inferInstance
  letI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass v)) :=
    Subgroup.isCyclic_of_le le_top
  letI : v.IsRankOneDiscrete := _root_.Valuation.IsRankOneDiscrete.mk' v
  exact ValuationTheory.Valuations.completeDVFOfCompleteValuedField

end Langlands.NYLL.LocalFieldTheory
