/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 205, 2026-11-13: extract the M266.007–.010 theorem
statements from commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL and close each original telescope
under universal quantifiers in a Prop-valued definition with a Statement
suffix. Import only the published data needed for these targets.
Source proofs and simp attributes are reserved for proof contributions.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U006.Definitions

/-!
# Multiplicative valuation modulo degree: proposition targets

Source: M266.007–.010 in
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`.
-/

universe u

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Evaluation is the multiplicative tag of the normalized valuation reduced modulo n. -/
def valuationModDegreeMulHom_applyStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) (x : Kˣ),
    valuationModDegreeMulHom K n x =
      Multiplicative.ofAdd
        (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) : ZMod n)

/-- Every multiplicatively tagged element of ZMod n is the image of a field unit. -/
def valuationModDegreeMulHom_surjectiveStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat),
    Function.Surjective (valuationModDegreeMulHom K n)

/-- A field unit maps to one exactly when n divides its normalized valuation. -/
def valuationModDegreeMulHom_eq_one_iff_dvdStatement : Prop :=
  ∀ (K : Type u) [Field K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) (x : Kˣ),
    valuationModDegreeMulHom K n x = 1 ↔
      (n : Int) ∣
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x)

/-- Two field units have equal images exactly when n divides their ordered valuation difference. -/
def valuationModDegreeMulHom_eq_iff_dvd_subStatement : Prop :=
  ∀ (K : Type u) [Field K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) (x y : Kˣ),
    valuationModDegreeMulHom K n x = valuationModDegreeMulHom K n y ↔
      (n : Int) ∣
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) -
          LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul y)

end Langlands.NYLL.LocalClassFieldTheory
