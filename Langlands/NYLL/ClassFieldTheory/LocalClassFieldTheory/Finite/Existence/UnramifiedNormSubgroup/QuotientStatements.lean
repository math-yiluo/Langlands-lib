/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 205, 2026-11-13: extract M266.014–.017 theorem
statements from commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL and close each original telescope
under universal quantifiers in a Prop-valued definition with a Statement
suffix. Import only the published quotient projection and its dependencies.
The source proofs are reserved for separate proof contributions.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U013.Definitions

/-!
# Unramified norm classes: proposition targets

Source: M266.014–.017 in `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`.
-/

universe u

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Every unramified norm class is represented by a field unit. -/
def unramifiedNormClass_surjectiveStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat),
    Function.Surjective (unramifiedNormClass K n)

/-- The kernel of the canonical quotient map is the published unramified norm subgroup. -/
def unramifiedNormClass_kerStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat),
    MonoidHom.ker (unramifiedNormClass K n) =
      unramifiedNormSubgroup K n

/-- A unit has trivial class exactly when n divides its normalized valuation. -/
def unramifiedNormClass_eq_one_iffStatement : Prop :=
  ∀ (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) (x : Kˣ),
    unramifiedNormClass K n x = 1 ↔
      (n : Int) ∣ LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul
        x)

/-- A unit has trivial class exactly when it belongs to the published subgroup. -/
def unramifiedNormClass_eq_one_iff_memStatement : Prop :=
  ∀ (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) (x : Kˣ),
    unramifiedNormClass K n x = 1 ↔ x ∈ unramifiedNormSubgroup K n

end Langlands.NYLL.LocalClassFieldTheory
