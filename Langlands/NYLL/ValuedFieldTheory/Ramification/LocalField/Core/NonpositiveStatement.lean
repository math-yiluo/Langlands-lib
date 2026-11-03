/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 60, 2026-11-03, with source extraction, proposition design
and dependency analysis contributed by Worker 106:
extract the statements of M327.017–M327.020 at upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 into one closed four-conjunct Prop;
prefix the namespace with Langlands.NYLL, import only the published local
group definitions, and bind the unchanged Type 0 telescope inside the Prop.
The original proofs are omitted. Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.Definitions

/-!
# Nonpositive local ramification laws

The closed statement of NYLL M327.017–M327.020 for the published actual local
lower and upper ramification groups.
-/

namespace Langlands.NYLL.RamificationTheory.LocalField

open Langlands.NYLL.LocalFieldTheory

/-- Upper and lower numbering agree at nonpositive indices, both filtrations
equal their index-zero groups on `(-1, 0]`, and the upper group is full at
and below `-1`, for every finite Galois extension of a local base field. -/
def LocalNonpositiveRamificationLawsStatement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    (∀ (t : ℝ), t ≤ 0 →
      localUpperRamificationGroup K L t = localLowerRamificationGroup K L t) ∧
    (∀ (t : ℝ), -1 < t → t ≤ 0 →
      localLowerRamificationGroup K L t = localLowerRamificationGroup K L 0) ∧
    (∀ (t : ℝ), -1 < t → t ≤ 0 →
      localUpperRamificationGroup K L t = localUpperRamificationGroup K L 0) ∧
    (∀ (t : ℝ), t ≤ -1 → localUpperRamificationGroup K L t = ⊤)

end Langlands.NYLL.RamificationTheory.LocalField
