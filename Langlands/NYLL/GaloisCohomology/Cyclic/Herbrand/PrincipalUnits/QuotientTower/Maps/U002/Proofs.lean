/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 750, 16 November 2026: extract the proof of M147.002 from
Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean at
fbd320cd8b1b06487c58227e92eb135794267709, lines 41–50. Add the Langlands.NYLL
namespace prefix, give the theorem the published target applied to its
parameters as its type, omit the `@[simp]` attribute, and import the target
module and the published proof of `integerUnitsModPrincipalUnitsAtLevelLift_mk`
instead of the source imports. The source proof term is unchanged. Omit the
source noncomputable section and all other source declarations. See the paired
Markdown; the original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.Maps.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.U009.Proofs

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The level-change map sends a unit class to the class of the same unit. -/
theorem integerUnitsModPrincipalUnitsMapOfLe_mk
    (K : Type u) [Field K] [ValuativeRel K] {n m : Nat} (hnm : n ≤ m)
    (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMapOfLe_mkStatement K hnm x :=
  integerUnitsModPrincipalUnitsAtLevelLift_mk m
    (integerUnitsModPrincipalUnitsAtLevelMk K n) _ x

end Langlands.NYLL.CyclicCohomology
