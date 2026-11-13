/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Adapted from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
-- QuotientReps.lean, lines 74–111. See Statements.md and licenses/NYLL/.

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.Definitions

/-!
# Statement targets for integer-unit quotients at a level

These proposition definitions retain the source theorem telescopes and
conclusions. Their proofs belong to separate proof tasks.
-/

namespace Langlands.NYLL.CyclicCohomology

open Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

set_option linter.unusedVariables false

/-- Target for elimination of a level quotient through canonical representatives. -/
protected def IntegerUnitsModPrincipalUnitsAtLevel.inductionOnStatement
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : IntegerUnitsModPrincipalUnitsAtLevel K n → Prop}
    (q : IntegerUnitsModPrincipalUnitsAtLevel K n)
    (h : ∀ x : 𝒪[K]ˣ,
      motive (integerUnitsModPrincipalUnitsAtLevelMk K n x)) :
    Prop :=
  motive q

/-- Target for a lifted homomorphism's value on canonical representatives. -/
def integerUnitsModPrincipalUnitsAtLevelLift_mkStatement
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (n : Nat) (f : 𝒪[K]ˣ →* M) (h : principalUnits K n ≤ f.ker)
    (x : 𝒪[K]ˣ) : Prop :=
  integerUnitsModPrincipalUnitsAtLevelLift n f h
      (integerUnitsModPrincipalUnitsAtLevelMk K n x) = f x

/-- Target for detection of principal units by the identity quotient class. -/
def integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iffStatement
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (x : 𝒪[K]ˣ) : Prop :=
  integerUnitsModPrincipalUnitsAtLevelMk K n x = 1 ↔
    x ∈ principalUnits K n

end

end Langlands.NYLL.CyclicCohomology
