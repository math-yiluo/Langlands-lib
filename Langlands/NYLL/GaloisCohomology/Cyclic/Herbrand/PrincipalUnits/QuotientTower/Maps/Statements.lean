/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.Maps.Definitions

/-!
# Targets: level-change maps of the finite principal-unit quotient tower

Modified by Worker 5264, 15 November 2026: state the source theorems M147.002
`integerUnitsModPrincipalUnitsMapOfLe_mk`, M147.004
`integerUnitsModPrincipalUnitsSuccMap_mk`, M147.011
`principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk`, M147.012
`integerUnitsSuccMap_comp_principalUnitsSuccQuot` and M147.013
`principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_ker` of
`Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean` at
fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to each name, omit the proofs, the `@[simp]` attributes and the rest of the
source file, and import the module of this port that defines the three maps
instead of the source imports. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/


namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Target: the level-change map sends a unit class to the class of the same
unit. -/
def integerUnitsModPrincipalUnitsMapOfLe_mkStatement
    (K : Type u) [Field K] [ValuativeRel K] {n m : Nat} (hnm : n ≤ m)
    (x : 𝒪[K]ˣ) : Prop :=
    integerUnitsModPrincipalUnitsMapOfLe K hnm
        (integerUnitsModPrincipalUnitsAtLevelMk K m x) =
      integerUnitsModPrincipalUnitsAtLevelMk K n x

/-- Target: the successor-level map sends a unit representative to its
successor quotient class. -/
def integerUnitsModPrincipalUnitsSuccMap_mkStatement
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (x : 𝒪[K]ˣ) : Prop :=
    integerUnitsModPrincipalUnitsSuccMap K n
        (integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) x) =
      integerUnitsModPrincipalUnitsAtLevelMk K n x

/-- Target: the principal-unit quotient map sends a representative to its
integer-unit class. -/
def principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mkStatement
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (u : principalUnits K n) : Prop :=
    principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n
        (principalUnitsSuccQuotMk K n u) =
      integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) (u : 𝒪[K]ˣ)

/-- Target: the principal-unit inclusion followed by the successor map is the
canonical quotient map. -/
def integerUnitsSuccMap_comp_principalUnitsSuccQuotStatement
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) : Prop :=
    (integerUnitsModPrincipalUnitsSuccMap K n).comp
        (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n) = 1

/-- Target: exactness of `U_K^n/U_K^(n+1) → 𝒪_Kˣ/U_K^(n+1) → 𝒪_Kˣ/U_K^n`
at the middle finite-filtration quotient. -/
def principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_kerStatement
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) : Prop :=
    MonoidHom.range (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n) =
      MonoidHom.ker (integerUnitsModPrincipalUnitsSuccMap K n)

end

end Langlands.NYLL.CyclicCohomology
