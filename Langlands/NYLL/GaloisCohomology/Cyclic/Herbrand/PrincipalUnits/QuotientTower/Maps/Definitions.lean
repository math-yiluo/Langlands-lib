/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.U010.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.U005.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.SuccessorDefinitions

/-!
# Level-change maps of the finite principal-unit quotient tower

Modified by Worker 5264, 15 November 2026: port the source definitions M147.001
`integerUnitsModPrincipalUnitsMapOfLe`, M147.003
`integerUnitsModPrincipalUnitsSuccMap` and M147.010
`principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc` of
`Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean` at
fbd320cd8b1b06487c58227e92eb135794267709 with their source binders, docstrings
and bodies. Prefix the namespace with `Langlands.NYLL`, import the four focused
published modules above instead of the four source imports, and omit the
other source declarations. In the embedded proofs of M147.001 and M147.010,
the source rewrite with `integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff`
is made with a local hypothesis `hmk` holding exactly that equivalence at the
relevant level, because the published theorem has a Prop-valued Statement
type, which `rw` cannot use directly. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/


namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The natural projection `𝒪_Kˣ/U_K^m → 𝒪_Kˣ/U_K^n` for `n ≤ m`. -/
def integerUnitsModPrincipalUnitsMapOfLe
    (K : Type u) [Field K] [ValuativeRel K] {n m : Nat} (hnm : n ≤ m) :
    IntegerUnitsModPrincipalUnitsAtLevel K m →*
      IntegerUnitsModPrincipalUnitsAtLevel K n :=
  integerUnitsModPrincipalUnitsAtLevelLift m
    (integerUnitsModPrincipalUnitsAtLevelMk K n)
    (by
      intro x hx
      have hmk : ∀ y : 𝒪[K]ˣ,
          integerUnitsModPrincipalUnitsAtLevelMk K n y = 1 ↔ y ∈ principalUnits K n :=
        fun y => integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff K n y
      rw [MonoidHom.mem_ker,
        hmk]
      exact principalUnits_antitone K hnm hx)

/-- The successive projection `𝒪_Kˣ/U_K^(n+1) → 𝒪_Kˣ/U_K^n`. -/
def integerUnitsModPrincipalUnitsSuccMap
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    IntegerUnitsModPrincipalUnitsAtLevel K (n + 1) →*
      IntegerUnitsModPrincipalUnitsAtLevel K n :=
  integerUnitsModPrincipalUnitsMapOfLe K (Nat.le_succ n)

/-- The graded quotient `U_K^n/U_K^(n+1)` as the kernel source inside
`𝒪_Kˣ/U_K^(n+1)`. -/
def principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    PrincipalUnitsSuccQuot K n →*
      IntegerUnitsModPrincipalUnitsAtLevel K (n + 1) :=
  principalUnitsSuccQuotLift n
    ((integerUnitsModPrincipalUnitsAtLevelMk K (n + 1)).comp
      (principalUnits K n).subtype)
    (by
      intro u hu
      have hmk : ∀ y : 𝒪[K]ˣ,
          integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) y = 1 ↔
            y ∈ principalUnits K (n + 1) :=
        fun y => integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff K (n + 1) y
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        hmk]
      exact hu)

end

end Langlands.NYLL.CyclicCohomology
