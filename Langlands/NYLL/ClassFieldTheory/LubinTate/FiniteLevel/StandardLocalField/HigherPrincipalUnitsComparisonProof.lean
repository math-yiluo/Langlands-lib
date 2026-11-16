/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 807, 2026-11-16: extract the proof of M335.014
(lines 204–227) from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL; import the focused published
statement; use that fully applied statement as the theorem type; replace
the call to M335.013 by a local definitional membership comparison.
See the paired Markdown. License and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.PrincipalUnitComparisonStatements

/-!
# Higher principal units of the standard local field

The canonical integer-unit equivalence identifies the packaged higher
principal-unit subgroup with the topology-first principal-unit subgroup.
-/

noncomputable section

open scoped ValuativeRel

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Mapping packaged higher principal units back through the canonical
integer-unit equivalence gives the topology-first principal-unit subgroup. -/
theorem standardLocalFieldHigherPrincipalUnitGroup_map_eq_principalUnits
    (n : ℕ) :
    standardLocalFieldHigherPrincipalUnitGroup_map_eq_principalUnitsStatement K n := by
  let e := standardLocalFieldIntegerUnitsEquiv K
  have hmem (u : 𝒪[K]ˣ) :
      e u ∈ higherPrincipalUnitGroup
          (standardLocalField K).toCompleteDVF n ↔
        u ∈ principalUnits K n :=
    Iff.rfl
  ext u
  constructor
  · rintro ⟨a, ha, rfl⟩
    change a ∈ higherPrincipalUnitGroup
      (standardLocalField K).toCompleteDVF n at ha
    exact (hmem (e.symm a)).1
      (by simpa only [e, MulEquiv.apply_symm_apply] using ha)
  · intro hu
    have heu :
        e u ∈ higherPrincipalUnitGroup
          (standardLocalField K).toCompleteDVF n :=
      (hmem u).2 hu
    exact ⟨e u, heu, e.symm_apply_apply u⟩

end Langlands.NYLL.LubinTate

end
