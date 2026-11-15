/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 85, 15 November 2026:
State only the theorems M166.002 (lines 65–80), M166.003 (108–128) and
M166.004 (172–199) of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
AbstractFixedFieldNorm.lean
at fbd320cd8b1b06487c58227e92eb135794267709, without their proofs, as
Prop-valued definitions named after the source theorems with the suffix
Statement. For M166.002 the section variables K, Ω and their five instance
binders (lines 31–32) become the leading binders, followed by the theorem's
own binders; M166.003 and M166.004 declare all their binders themselves and
keep them. Binders, their kinds, names and order, and the propositions are
the source text. Add the Langlands.NYLL namespace prefix. Import the Library
modules that publish the names used, and Mathlib.RingTheory.Valuation.Extension
for Valuation.HasExtension, instead of the source imports. Silence the
unused-variable linter for M166.004, whose named instance binder
hIntegralClosure is kept from the source. Omit the
proofs, the noncomputable section and all other declarations. The original
LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.HenselianValuationBase.U001.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions
import Mathlib.RingTheory.Valuation.Extension

/-!
# Finite local reciprocity: the norm of a finite abstract field, targets

Closed propositions comparing, for a closed subgroup `H` of a Galois group
`Gal(Ω/K)` with finite separable fixed field `E = Ω^H`, the class-formation
norm `normToBase` from the `H`-fixed units to the base-fixed units with the
field norm `E → K` (M166.002); for a nonarchimedean local field `K` with
`Ω = SeparableClosure K`, the base valuation of that norm (M166.003) and the
range of the base valuation after the norm (M166.004).

NYLL's `valuationMap` is the negative of the usual normalized order: a prime
element of the valuation ring has value `-1`. M166.003 is an equality of
values and holds for either sign; M166.004 only uses value groups, which the
sign does not change.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology KummerTheory ClassFormation

open LocalFieldTheory

open scoped ValuativeRel

/-- States the theorem `normToBase_abstractFixedFieldUnit_val_of_isSeparable`
(M166.002): for an arbitrary finite separable abstract field, the abstract
class-formation norm on fixed coefficients has the same underlying field
element as the ordinary field norm from its concrete fixed field. -/
def normToBase_abstractFixedFieldUnit_val_of_isSeparableStatement
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsSepClosed Ω]
    (H : ClosedSubgroup (Gal(Ω/K)))
    [Finite ((baseField (Gal(Ω/K))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/K))) H (le_baseField H))]
    [FiniteDimensional K (abstractFixedField K Ω H)]
    [Algebra.IsSeparable K (abstractFixedField K Ω H)]
    (x : (abstractFixedField K Ω H)ˣ) : Prop :=
  ((Additive.toMul
    ((normToBase (galoisAmbientUnitsRep K Ω) H
      (abstractFixedFieldUnitsEquivGaloisFixed K Ω H
        (Additive.ofMul x))).1 : Additive Ωˣ) : Ωˣ) : Ω) =
    algebraMap K Ω (Algebra.norm K
      (x : abstractFixedField K Ω H))

/-- States the theorem `localBaseValuation_normToBase_abstractFixedFieldUnit`
(M166.003): the base normalized valuation of the abstract norm is the
ordinary normalized valuation of the concrete field norm. -/
def localBaseValuation_normToBase_abstractFixedFieldUnitStatement
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : ClosedSubgroup (Gal(SeparableClosure K/K)))
    [Finite ((baseField (Gal(SeparableClosure K/K))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(SeparableClosure K/K))) H
        (le_baseField H))]
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H)]
    (x : (abstractFixedField K (SeparableClosure K) H)ˣ) : Prop :=
  localBaseValuation K
      (normToBase
        (galoisAmbientUnitsRep K (SeparableClosure K)) H
        (abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) H (Additive.ofMul x))) =
    Int.castRingHom ZHat
      (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
        (Additive.ofMul
          (normUnits K (abstractFixedField K (SeparableClosure K) H) x)))

-- The source instance-binder name `hIntegralClosure` is kept although the
-- proposition never mentions it.
set_option linter.unusedVariables false in
/-- States the theorem
`localBaseValuation_comp_normToBase_range_eq_residueFinrank` (M166.004): for
an arbitrary finite separable abstract field, the image of the base
valuation after the abstract class-formation norm is exactly the actual
residue-degree multiple of the base value group. -/
def localBaseValuation_comp_normToBase_range_eq_residueFinrankStatement
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : ClosedSubgroup (Gal(SeparableClosure K/K)))
    [Finite ((baseField (Gal(SeparableClosure K/K))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(SeparableClosure K/K))) H
        (le_baseField H))]
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H)]
    [ValuativeRel (abstractFixedField K (SeparableClosure K) H)]
    [TopologicalSpace (abstractFixedField K (SeparableClosure K) H)]
    [IsNonarchimedeanLocalField
      (abstractFixedField K (SeparableClosure K) H)]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation
        (abstractFixedField K (SeparableClosure K) H))]
    [hIntegralClosure : IsIntegralClosure
      𝒪[abstractFixedField K (SeparableClosure K) H] 𝒪[K]
      (abstractFixedField K (SeparableClosure K) H)] : Prop :=
  ((localBaseValuation K).comp
    (normToBase
      (galoisAmbientUnitsRep K (SeparableClosure K)) H)).range =
    nsmulImage (localBaseValuation K).range
      (Module.finrank 𝓀[K]
        𝓀[abstractFixedField K (SeparableClosure K) H])

end Langlands.NYLL.LocalClassFieldTheory
