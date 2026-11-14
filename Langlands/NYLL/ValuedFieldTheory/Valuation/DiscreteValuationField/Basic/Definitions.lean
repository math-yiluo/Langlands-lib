/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 171, 14 November 2026: extract source units M103.001,
M103.031, M103.032, M103.033, M103.034 and M103.036 (lines 28-30 and 319-370)
from upstream fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespaces
with Langlands.NYLL and import the published DVF data module instead of
redefining it. The declarations, binders and bodies are otherwise unchanged.
Source units M103.004-M103.006 are canonical Mathlib instance reuse; the
`example` commands at the end only check that reuse against the source
telescope and add no declaration. See the paired Markdown for details.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Mathlib.Algebra.CharP.Subring
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic

/-!
# Characteristic of valuation subrings and successive maximal-ideal quotients

Adapted from lines 28-30 and 319-370 of
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean`.
-/

namespace Langlands.NYLL.ValuationTheory

noncomputable section

universe u v

namespace ValuationSubring

/-- A valuation subring has the characteristic of its ambient field. -/
instance charP {K : Type u} [Field K] (R : ValuationSubring K) (p : ℕ) [CharP K p] :
    CharP R p :=
  CharP.subring K p R.toSubring

end ValuationSubring

namespace DiscreteValuationField

namespace DVF

variable {K : Type u} [Field K]

/-! ### Successive quotients of powers of the maximal ideal -/

/-- The submodule `m^(n+1)` inside `m^n`. -/
abbrev maximalIdealPowSuccSubmodule (F : DVF.{u, v} K) (n : ℕ) :
    Submodule F.valuationSubring ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) :=
  Submodule.comap (Submodule.subtype (p := (F.maximalIdeal ^ n : Ideal F.valuationSubring)))
    ((F.maximalIdeal ^ (n + 1) : Ideal F.valuationSubring) :
      Submodule F.valuationSubring F.valuationSubring)

/-- The additive ideal-power quotient `m^n/m^(n+1)`. -/
def MaximalIdealPowSuccQuot (F : DVF.{u, v} K) (n : ℕ) : Type u :=
  ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
    F.maximalIdealPowSuccSubmodule n

/-- A successive maximal-ideal quotient is an additive commutative group. -/
instance maximalIdealPowSuccQuotAddCommGroup
    (F : DVF.{u, v} K) (n : ℕ) :
    AddCommGroup (F.MaximalIdealPowSuccQuot n) := by
  change AddCommGroup
    (((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
      F.maximalIdealPowSuccSubmodule n)
  infer_instance

/-- A successive maximal-ideal quotient is a module over the valuation subring. -/
instance maximalIdealPowSuccQuotModule
    (F : DVF.{u, v} K) (n : ℕ) :
    Module F.valuationSubring (F.MaximalIdealPowSuccQuot n) := by
  change Module F.valuationSubring
    (((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
      F.maximalIdealPowSuccSubmodule n)
  infer_instance

/-- The quotient map `m^n → m^n/m^(n+1)`. -/
def maximalIdealPowSuccQuotMk (F : DVF.{u, v} K) (n : ℕ) :
    ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) →ₗ[F.valuationSubring]
      F.MaximalIdealPowSuccQuot n := by
  change
    ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)
      →ₗ[F.valuationSubring]
        (((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
          F.maximalIdealPowSuccSubmodule n)
  exact Submodule.mkQ (F.maximalIdealPowSuccSubmodule n)

/-! ### Focused checks for the canonical instance reuse of M103.004-M103.006

Each check uses the complete source telescope of the omitted source instance.
Instance search on the published `valuationSubring` abbreviation must succeed
and, for the data-carrying ring structure, agree with the source body. -/

/- M103.004, source line 58: the source body is the canonical Mathlib ring. -/
example (F : DVF.{u, v} K) :
    (inferInstance : CommRing F.valuationSubring) =
      ValuationSubring.instCommRingSubtypeMem F.valuation.valuationSubring :=
  rfl

/- M103.005, source line 63: the source body has the synthesized type. -/
example (F : DVF.{u, v} K) : IsLocalRing F.valuationSubring :=
  ValuationSubring.isLocalRing F.valuation.valuationSubring

example (F : DVF.{u, v} K) : IsLocalRing F.valuationSubring :=
  inferInstance

/- M103.006, source line 68: the source body has the synthesized type. -/
example (F : DVF.{u, v} K) : IsDomain F.valuationSubring :=
  ValuationSubring.instIsDomainSubtypeMem F.valuation.valuationSubring

example (F : DVF.{u, v} K) : IsDomain F.valuationSubring :=
  inferInstance

end DVF

end DiscreteValuationField

end

end Langlands.NYLL.ValuationTheory
