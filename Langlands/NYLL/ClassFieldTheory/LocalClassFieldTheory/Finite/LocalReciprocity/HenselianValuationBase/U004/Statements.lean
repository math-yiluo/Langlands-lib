/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 85, 15 November 2026:
State only the theorems M163.004 (lines 49–56), M163.006 (73–78), M163.007
(81–85), M163.008 (97–100), M163.010 (110–112), M163.011 (121–124) and
M163.013 (167–171) of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
HenselianValuationBase.lean
at fbd320cd8b1b06487c58227e92eb135794267709, without their proofs, as closed
propositions named after the source theorems with the suffix Statement. The
section variables K and its instance binders (lines 32–33) become leading
universal binders, followed by each theorem's own binders; for M163.004 the
three instances omitted by the source `omit` line are left out. Add the
Langlands.NYLL namespace prefix. Import the Library modules that publish
localBaseValuation, baseFieldUnitsEquiv, localValueGroupReduction,
nsmulWithin and canonicalValueQuotientMap instead of the source imports. Omit
the proofs, the `@[simp]` attributes of M163.004 and M163.006, the
noncomputable section and all other declarations. The original LICENSE and
NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.HenselianValuationBase.U001.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.Definitions

/-!
# Finite local reciprocity: the base value group in `ℤ̂`, targets

Closed propositions about a nonarchimedean local field `K`: the value of the
identification of `Kˣ` with the base-fixed coefficients (M163.004), the
values of the transported valuation `localBaseValuation K` (M163.006), its
range is the image of `ℤ` in `ℤ̂` (M163.007, M163.008), and its reduction
modulo `n` is surjective with kernel `n` times the value group (M163.010,
M163.011), so that the canonical map from the value group modulo `n` to
`ZMod n` is bijective (M163.013).

NYLL's `valuationMap` is the negative of the usual normalized order: a prime
element of the valuation ring has value `-1`. The targets only use the value
group, which this sign does not change.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory KummerTheory

open LocalFieldTheory

open ClassFormation

/-- Closed target for NYLL M163.004 `baseFieldUnitsEquiv_val`: the element
of the separable closure underlying `baseFieldUnitsEquiv K x` is the image
of `x` under the algebra map. -/
def baseFieldUnitsEquiv_valStatement : Prop :=
  ∀ (K : Type) [Field K] (x : Kˣ),
    ((Additive.toMul
      ((baseFieldUnitsEquiv K (Additive.ofMul x)).1 :
        Additive (SeparableClosure K)ˣ) : (SeparableClosure K)ˣ) :
      SeparableClosure K) = algebraMap K (SeparableClosure K) (x : K)

/-- Closed target for NYLL M163.006
`localBaseValuation_baseFieldUnitsEquiv`: on the image of a unit `x`, the
transported valuation is NYLL's `valuationMap` value of `x`, cast to `ℤ̂`. -/
def localBaseValuation_baseFieldUnitsEquivStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Additive Kˣ),
    localBaseValuation K (baseFieldUnitsEquiv K x) =
      Int.castRingHom ZHat
        (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x)

/-- Closed target for NYLL M163.007 `localBaseValuation_range`: the value
group is exactly the image of the ordinary integers in the profinite
integers. -/
def localBaseValuation_rangeStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    (localBaseValuation K).range =
      (Int.castRingHom ZHat).toAddMonoidHom.range

/-- Closed target for NYLL M163.008
`intToProCInteger_mem_localBaseValuation_range`: every ordinary integer,
cast to `ℤ̂`, is a value. -/
def intToProCInteger_mem_localBaseValuation_rangeStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (m : ℤ),
    Int.castRingHom ZHat m ∈
      (localBaseValuation K).range

/-- Closed target for NYLL M163.010 `localValueGroupReduction_surjective`:
reduction modulo `n` on the value group is surjective. -/
def localValueGroupReduction_surjectiveStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) (hn : 0 < n),
    Function.Surjective (localValueGroupReduction K n hn)

/-- Closed target for NYLL M163.011 `localValueGroupReduction_ker`: the
kernel of reduction modulo `n` on the value group is `n` times the value
group. -/
def localValueGroupReduction_kerStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) (hn : 0 < n),
    (localValueGroupReduction K n hn).ker =
      nsmulWithin (localBaseValuation K).range n

/-- Closed target for NYLL M163.013
`localCanonicalValueQuotientMap_bijective`: the canonical map from the value
group modulo `n` to `ZMod n`, induced by inclusion into `ℤ̂` and reduction,
is bijective. -/
def localCanonicalValueQuotientMap_bijectiveStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) (hn : 0 < n),
    Function.Bijective
      (canonicalValueQuotientMap (localBaseValuation K).range n hn)

end Langlands.NYLL.LocalClassFieldTheory
