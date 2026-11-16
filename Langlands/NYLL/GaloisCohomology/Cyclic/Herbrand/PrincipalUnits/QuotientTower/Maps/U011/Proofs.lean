/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 750, 16 November 2026: extract the proof of M147.011 from
Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean at
fbd320cd8b1b06487c58227e92eb135794267709, lines 180–190. Add the
Langlands.NYLL namespace prefix, give the theorem the published target
applied to its parameters as its type and omit the `@[simp]` attribute. The
source proof applies M132.006 `principalUnitsSuccQuotLift_mk`, whose proof is
not yet in the Library; this proof is `rfl`, the definitional evaluation of
the quotient lift on a representative. Import only the target module. Omit the
source noncomputable section and all other source declarations. See the paired
Markdown; the original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.Maps.Statements

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The principal-unit quotient map sends a representative to its integer-unit
class. -/
theorem principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (u : principalUnits K n) :
    principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mkStatement K n u :=
  rfl

end Langlands.NYLL.CyclicCohomology
