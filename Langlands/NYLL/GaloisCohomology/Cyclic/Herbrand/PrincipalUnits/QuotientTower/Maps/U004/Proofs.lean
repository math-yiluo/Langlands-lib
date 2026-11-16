/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 750, 16 November 2026: extract the proof of M147.004 from
Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean at
fbd320cd8b1b06487c58227e92eb135794267709, lines 59–67. Add the Langlands.NYLL
namespace prefix, give the theorem the published target applied to its
parameters as its type and omit the `@[simp]` attribute. The source proof
applies M147.002 `integerUnitsModPrincipalUnitsMapOfLe_mk`, whose proof is not
yet in the Library; this proof instead applies the published
`integerUnitsModPrincipalUnitsAtLevelLift_mk` at level `n + 1`, the term
proving M147.002, ascribed the M147.002 target at `Nat.le_succ n`. Import the
target module and that published proof instead of the source imports. Omit
the source noncomputable section and all other source declarations. See the
paired Markdown; the original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.Maps.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.U009.Proofs

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The successor-level map sends a unit representative to its successor
quotient class. -/
theorem integerUnitsModPrincipalUnitsSuccMap_mk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsSuccMap_mkStatement K n x :=
  (integerUnitsModPrincipalUnitsAtLevelLift_mk (n + 1)
    (integerUnitsModPrincipalUnitsAtLevelMk K n) _ x :
      integerUnitsModPrincipalUnitsMapOfLe_mkStatement K (Nat.le_succ n) x)

end Langlands.NYLL.CyclicCohomology
