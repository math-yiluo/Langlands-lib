/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Adapted by Worker 211 from pinned NYLL PrincipalUnitQuotients.lean.
-- See the paired Markdown for source lines, exact modifications and attribution.

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions
import Mathlib.LinearAlgebra.Quotient.Basic

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

open Filter

/-- The submodule `𝓂^(n+1)` inside `𝓂^n`. -/
abbrev maximalIdealPowSuccSubmodule
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    Submodule (𝒪[K]) ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) :=
  Submodule.comap (Submodule.subtype (p := (𝓂[K] ^ n : Ideal 𝒪[K])))
    ((𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) : Submodule (𝒪[K]) (𝒪[K]))

/-- The additive ideal-power quotient `𝓂^n/𝓂^(n+1)`. -/
def MaximalIdealPowSuccQuot
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) : Type u :=
  ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸ maximalIdealPowSuccSubmodule K n

/-- Equips the additive quotient `𝓂^n/𝓂^(n+1)` with its additive commutative group structure. -/
instance maximalIdealPowSuccQuotAddCommGroup
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    AddCommGroup (MaximalIdealPowSuccQuot K n) := by
  change AddCommGroup
    (((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n)
  infer_instance

/-- Equips `𝓂^n/𝓂^(n+1)` with the module structure induced from the valuation ring. -/
instance maximalIdealPowSuccQuotModule
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    Module 𝒪[K] (MaximalIdealPowSuccQuot K n) := by
  change Module 𝒪[K]
    (((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n)
  infer_instance

/-- The quotient map `𝓂^n → 𝓂^n/𝓂^(n+1)`. -/
def maximalIdealPowSuccQuotMk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) →ₗ[𝒪[K]]
      MaximalIdealPowSuccQuot K n := by
  change ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) →ₗ[𝒪[K]]
    (((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n)
  exact Submodule.mkQ (maximalIdealPowSuccSubmodule K n)

/-- Descend an arbitrary representative-level function that is constant
modulo `𝓂^(n+1)`. -/
def maximalIdealPowSuccQuotLift
    {K : Type u} {P : Sort*} [Field K] [ValuativeRel K] (n : Nat)
    (f : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) → P)
    (h : ∀ a b, a - b ∈ maximalIdealPowSuccSubmodule K n →
      f a = f b) :
    MaximalIdealPowSuccQuot K n → P := by
  change
    ((((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n) → P)
  refine Quotient.lift f ?_
  intro a b hab
  have hq :
      (Submodule.Quotient.mk a :
        ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
          maximalIdealPowSuccSubmodule K n) =
        Submodule.Quotient.mk b :=
    Quotient.sound hab
  exact h a b
    ((Submodule.Quotient.eq (maximalIdealPowSuccSubmodule K n)).1 hq)

end

end Langlands.NYLL.LocalFieldTheory
