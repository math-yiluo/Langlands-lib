/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 134, 14 November 2026: extract the proof of M147.023 from
Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean at
fbd320cd8b1b06487c58227e92eb135794267709, lines 459–469. Add the
Langlands.NYLL namespace prefix, give the theorem the published target
applied to its parameters as its type, import the target module and the
published proof of `principalUnits_zero`, and rewrite with that theorem
through a local equation because its published type is a closed `Statement`
proposition. Omit the source noncomputable section and all other source
declarations. See the paired Markdown; the original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.FinitenessStatements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Proofs

/-!
# Finiteness of the zeroth principal-unit quotient

The quotient `𝒪_Kˣ/U_K^0` is finite because `U_K^0` is all of `𝒪_Kˣ`.
-/

namespace Langlands.NYLL.CyclicCohomology

open Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The quotient `𝒪_Kˣ/U_K^0` is finite because `U_K^0 = 𝒪_Kˣ`. -/
theorem integerUnitsModPrincipalUnitsAtLevel_finite_zero
    (K : Type u) [Field K] [ValuativeRel K] :
    integerUnitsModPrincipalUnitsAtLevel_finite_zeroStatement K := by
  have h₀ : principalUnits K 0 = ⊤ := principalUnits_zero K
  let : Finite (𝒪[K]ˣ ⧸ principalUnits K 0) := by
    rw [h₀]
    infer_instance
  exact Finite.of_equiv (𝒪[K]ˣ ⧸ principalUnits K 0)
    (integerUnitsModPrincipalUnitsAtLevelConcreteEquiv K 0).symm.toEquiv

end Langlands.NYLL.CyclicCohomology
