/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 147, 13 November 2026:
Extract the proof of M132.068 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean
at fbd320cd8b1b06487c58227e92eb135794267709, lines 911–918. Add the Langlands.NYLL
namespace prefix. Keep the source telescope and give the theorem the published
target applied to its parameters as its type; the original proof term `Iff.rfl` is
kept unchanged. Import only QuotientAlgebraStatements. Omit the source
noncomputable section and all other source declarations. The original LICENSE and
NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.QuotientAlgebraStatements

/-!
# Membership in the submodule `𝓂^(n+1)` of `𝓂^n`

An element of `𝓂^n` belongs to the defining submodule of `𝓂^n/𝓂^(n+1)` exactly
when its value lies in `𝓂^(n+1)`.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- An element of `𝓂^n` belongs to the defining submodule exactly when its value lies in
`𝓂^(n+1)`. -/
theorem mem_maximalIdealPowSuccSubmodule_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    mem_maximalIdealPowSuccSubmodule_iffStatement K n a :=
  Iff.rfl

end Langlands.NYLL.LocalFieldTheory
