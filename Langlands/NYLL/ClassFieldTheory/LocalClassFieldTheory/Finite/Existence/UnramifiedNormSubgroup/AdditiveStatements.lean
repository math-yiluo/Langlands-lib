/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 205, 2026-11-13: extract the M266.002–.005 theorem
statements from commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL, close the original telescopes
under universal quantifiers in Prop-valued definitions with Statement
suffixes, and import only the published M266.001 definition. Proofs and
simp attributes are left to separate proof contributions.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U001.Definitions

/-!
# Additive valuation modulo degree: proposition targets

Source: M266.002–.005 in
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`.
-/

universe u

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Evaluation of the reduced valuation is integer reduction of the published normalized unit valuation. -/
def valuationModDegree_applyStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) (x : Additive Kˣ),
    valuationModDegree K n x =
      (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x : ZMod n)

/-- Every element of ZMod n is a reduced normalized unit valuation. -/
def valuationModDegree_surjectiveStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat),
    Function.Surjective (valuationModDegree K n)

/-- The reduced valuation is zero exactly when the natural degree, cast to Int, divides the normalized unit valuation. -/
def valuationModDegree_eq_zero_iff_dvdStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) (x : Additive Kˣ),
    valuationModDegree K n x = 0 ↔
      (n : Int) ∣ LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x

/-- Two reduced valuations agree exactly when the natural degree, cast to Int, divides the difference of the normalized unit valuations. -/
def valuationModDegree_eq_iff_dvd_subStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) (x y : Additive Kˣ),
    valuationModDegree K n x = valuationModDegree K n y ↔
      (n : Int) ∣
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x -
          LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K y

end Langlands.NYLL.LocalClassFieldTheory
