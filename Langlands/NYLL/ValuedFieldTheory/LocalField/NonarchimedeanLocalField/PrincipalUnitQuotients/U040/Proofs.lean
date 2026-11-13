/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 147, 13 November 2026:
Extract the proof of M132.040 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean
at fbd320cd8b1b06487c58227e92eb135794267709, lines 594–599. Add the Langlands.NYLL
namespace prefix. Keep the source telescope and give the theorem the published
target applied to its parameters as its type; the original proof term is kept
unchanged. Import only QuotientAlgebraStatements. Omit the source noncomputable
section and all other source declarations. The original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.QuotientAlgebraStatements

/-!
# Surjectivity of the successive principal-unit quotient map

Every class in `U^n/U^(n+1)` is the class of a principal unit in `U^n`.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- Every class in `U^n/U^(n+1)` has a representative in `U^n`. -/
theorem principalUnitsSuccQuotMk_surjective
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    principalUnitsSuccQuotMk_surjectiveStatement K n :=
  QuotientGroup.mk'_surjective ((principalUnits K (n + 1)).subgroupOf (principalUnits K n))

end Langlands.NYLL.LocalFieldTheory
