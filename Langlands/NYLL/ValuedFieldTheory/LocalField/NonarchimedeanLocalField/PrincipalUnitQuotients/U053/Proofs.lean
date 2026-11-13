/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 147, 13 November 2026:
Extract the proof of M132.053 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean
at fbd320cd8b1b06487c58227e92eb135794267709, lines 739–747. Add the Langlands.NYLL
namespace prefix. Keep the source telescope and give the theorem the published
target applied to its parameters as its type; a leading `show` unfolds that target
to the source conclusion. The source rewrite with `mem_principalUnits_iff` is kept,
applied explicitly to its arguments because the published M131.002 theorem has a
closed proposition as its type. Import QuotientAlgebraStatements and the published
PrincipalUnits proofs. Omit the source noncomputable section and all other source
declarations. The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.QuotientAlgebraStatements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Proofs

/-!
# Membership in the embedded successor subgroup

A principal unit of `U^n` lies in the embedded subgroup `U^(n+1)` exactly when it
is congruent to one modulo `𝓂^(n+1)`.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- Membership in the embedded subgroup `U^(n+1)` is equivalent to congruence to one modulo
`𝓂^(n+1)`. -/
theorem mem_principalUnits_succ_subgroupOf_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (u : principalUnits K n) :
    mem_principalUnits_succ_subgroupOf_iffStatement K n u := by
  show u ∈ (principalUnits K (n + 1)).subgroupOf (principalUnits K n) ↔
      (((u : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])
  rw [Subgroup.mem_subgroupOf, mem_principalUnits_iff K (u : 𝒪[K]ˣ) (n + 1)]

end Langlands.NYLL.LocalFieldTheory
