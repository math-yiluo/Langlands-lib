/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 560 on 14 November 2026: isolate source unit M289.004,
prefix the namespace with Langlands.NYLL, import the focused neighborhood
proof, and state the result as the existing fully applied Library target.
The source telescope and proof term are retained.
See Proofs.md and licenses/NYLL/ for source correspondence and attribution.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups.U003.Proofs

/-!
# Principal units inside an open subgroup

Apply the neighborhood theorem to the open subgroup at its identity.
-/

noncomputable section

namespace Langlands.NYLL.LocalFieldTheory

open scoped ValuativeRel

universe u

/-- Every open subgroup contains a positive principal-unit subgroup. -/
theorem exists_fieldPrincipalUnits_le_of_isOpen
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : Subgroup Kˣ) (hH : IsOpen (H : Set Kˣ)) :
    exists_fieldPrincipalUnits_le_of_isOpenStatement K H hH :=
  exists_fieldPrincipalUnits_subset_of_mem_nhds K H (hH.mem_nhds H.one_mem)

end Langlands.NYLL.LocalFieldTheory
