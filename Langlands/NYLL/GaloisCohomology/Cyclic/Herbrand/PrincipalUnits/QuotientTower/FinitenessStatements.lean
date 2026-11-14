/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 111, 14 November 2026: extract the theorem units M147.023–.026
of NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean`
(lines 458–518), as Prop-valued definitions with the `Statement` suffix,
prefix the namespace with `Langlands.NYLL`, reuse the published quotients by
Lean name and reduce the imports. Universes, binders and propositions are
unchanged; no proof is supplied. See the paired Markdown; the LICENSE and
NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.SuccessorDefinitions
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Finiteness of the principal-unit quotient tower: statements

The exact propositions of the four source theorems asserting that the quotient
`𝒪_Kˣ/U_K^n` of integer units by the `n`-th principal units is finite.
-/

namespace Langlands.NYLL.CyclicCohomology

open Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Source M147.023: the quotient `𝒪_Kˣ/U_K^0` is finite. -/
def integerUnitsModPrincipalUnitsAtLevel_finite_zeroStatement
    (K : Type u) [Field K] [ValuativeRel K] : Prop :=
  Finite (IntegerUnitsModPrincipalUnitsAtLevel K 0)

/-- Source M147.024: over a nonarchimedean local field the quotient
`𝒪_Kˣ/U_K^1` is finite. -/
def integerUnitsModPrincipalUnitsAtLevel_finite_one_of_isNonarchimedeanLocalFieldStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Prop :=
  Finite (IntegerUnitsModPrincipalUnitsAtLevel K 1)

/-- Source M147.025: finiteness of `U_K^n/U_K^(n+1)` and of `𝒪_Kˣ/U_K^n`
gives finiteness of `𝒪_Kˣ/U_K^(n+1)`. -/
def integerUnitsModPrincipalUnitsAtLevel_finite_succ_of_finiteStatement
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    [Finite (PrincipalUnitsSuccQuot K n)]
    [Finite (IntegerUnitsModPrincipalUnitsAtLevel K n)] : Prop :=
  Finite (IntegerUnitsModPrincipalUnitsAtLevel K (n + 1))

/-- Source M147.026: over a nonarchimedean local field every quotient
`𝒪_Kˣ/U_K^n` is finite. -/
def integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalFieldStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) : Prop :=
  Finite (IntegerUnitsModPrincipalUnitsAtLevel K n)

end

end Langlands.NYLL.CyclicCohomology
