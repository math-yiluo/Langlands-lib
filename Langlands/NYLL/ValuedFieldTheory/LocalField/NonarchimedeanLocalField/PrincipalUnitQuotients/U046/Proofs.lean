/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 147, 13 November 2026:
Extract the proof of M132.046 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean
at fbd320cd8b1b06487c58227e92eb135794267709, lines 655–673. Add the Langlands.NYLL
namespace prefix. Keep the source telescope and give the theorem the published
target applied to its parameters as its type; a leading `show` unfolds that target
to the source conclusion. The two closing `simpa using` steps, which fail in the
approved Mathlib, are replaced by `exact` with the same terms; the rest of the
original proof is followed unchanged. Import only QuotientAlgebraStatements. Omit the source noncomputable section and
all other source declarations. The original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.QuotientAlgebraStatements

/-!
# The trivial successive principal-unit class

A principal unit of `U^n` has trivial class in `U^n/U^(n+1)` exactly when it lies
in the embedded subgroup `U^(n+1)`.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The class of a principal unit is trivial exactly when the unit belongs to `U^(n+1)`. -/
theorem principalUnitsSuccQuotMk_eq_one_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (u : principalUnits K n) :
    principalUnitsSuccQuotMk_eq_one_iffStatement K n u := by
  show principalUnitsSuccQuotMk K n u = 1 ↔
      u ∈ (principalUnits K (n + 1)).subgroupOf (principalUnits K n)
  constructor
  · intro h
    apply (QuotientGroup.eq_one_iff
      (N := (principalUnits K (n + 1)).subgroupOf (principalUnits K n)) u).mp
    have h' := congrArg (principalUnitsSuccQuotConcreteEquiv K n) h
    exact h'
  · intro h
    apply (principalUnitsSuccQuotConcreteEquiv K n).injective
    exact
      (QuotientGroup.eq_one_iff
        (N := (principalUnits K (n + 1)).subgroupOf (principalUnits K n)) u).mpr h

end Langlands.NYLL.LocalFieldTheory
