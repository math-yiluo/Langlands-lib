/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 147, 13 November 2026:
Extract the proof of M132.048 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean
at fbd320cd8b1b06487c58227e92eb135794267709, lines 692–707. Add the Langlands.NYLL
namespace prefix. Keep the source telescope and give the theorem the published
target applied to its parameters as its type; a leading `show` unfolds that target
to the source conclusion, after which the original proof is followed unchanged.
Import only QuotientAlgebraStatements. Omit the source noncomputable section and
all other source declarations. The original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.QuotientAlgebraStatements

/-!
# Equality of successive principal-unit classes

Two principal units in `U^n` have the same class in `U^n/U^(n+1)` exactly when
their quotient lies in the embedded subgroup `U^(n+1)`.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- Two principal units define the same successive-quotient class exactly when their quotient lies
in `U^(n+1)`. -/
theorem principalUnitsSuccQuotMk_eq_iff_div_mem
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (u v : principalUnits K n) :
    principalUnitsSuccQuotMk_eq_iff_div_memStatement K n u v := by
  show principalUnitsSuccQuotMk K n u = principalUnitsSuccQuotMk K n v ↔
      u / v ∈ (principalUnits K (n + 1)).subgroupOf (principalUnits K n)
  constructor
  · intro h
    have h' := congrArg (principalUnitsSuccQuotConcreteEquiv K n) h
    exact (QuotientGroup.eq_iff_div_mem
      (N := (principalUnits K (n + 1)).subgroupOf (principalUnits K n))).mp h'
  · intro h
    apply (principalUnitsSuccQuotConcreteEquiv K n).injective
    exact (QuotientGroup.eq_iff_div_mem
      (N := (principalUnits K (n + 1)).subgroupOf (principalUnits K n))).mpr h

end Langlands.NYLL.LocalFieldTheory
