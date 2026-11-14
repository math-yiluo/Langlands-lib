/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 545, 2026-11-14: extract the four M308.005–.008
endpoint signatures from commit fbd320cd8b1b06487c58227e92eb135794267709
as closed Prop-valued targets with suffix Statement. Prefix namespaces with
Langlands.NYLL, retain all source universes and hypotheses, and use focused
published imports. Omit the orbit-polynomial construction and all proofs.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.UniqueExtension
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs

/-!
# Unique-extension valuation-ring integrality, integral closure and finiteness targets

The four closed propositions below retain the full context of NYLL M308.005–.008.
The scalar algebra is the existing valuation-subring algebra supplied by
`Valuation.HasExtension`; no integrality or finiteness result is assumed.
-/

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

/-- Every element of the target valuation ring is integral over the base valuation ring. -/
def target_valuationSubring_element_isIntegral_of_uniqueExtensionStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    [FiniteDimensional K L] [base.valuation.HasExtension target.valuation]
    [IsGalois K L]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (a : target.valuationSubring),
    IsIntegral base.valuationSubring a

/-- The target valuation ring is an integral algebra over the base valuation ring. -/
def target_valuationSubring_isIntegral_of_uniqueExtensionStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    [FiniteDimensional K L] [base.valuation.HasExtension target.valuation]
    [IsGalois K L]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target),
    Algebra.IsIntegral base.valuationSubring target.valuationSubring

/-- The target valuation ring is the integral closure of the base valuation ring in `L`. -/
def target_valuationSubring_isIntegralClosure_of_uniqueExtensionStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    [FiniteDimensional K L] [base.valuation.HasExtension target.valuation]
    [IsGalois K L]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target),
    IsIntegralClosure target.valuationSubring base.valuationSubring L

/-- The target valuation ring is finitely generated as a module over the base valuation ring. -/
def target_valuationSubring_moduleFinite_of_uniqueExtensionStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    [FiniteDimensional K L] [base.valuation.HasExtension target.valuation]
    [IsGalois K L]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target),
    Module.Finite base.valuationSubring target.valuationSubring

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
