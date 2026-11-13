/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 296, 2026-11-13: extract the indicated source proposition(s)
from commit fbd320cd8b1b06487c58227e92eb135794267709 as closed Prop-valued
targets; prefix namespaces with Langlands.NYLL and use focused published
imports. Preserve source universes and hypotheses; omit proofs and attributes.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.Definitions

universe u v w x y

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

def lowerRamificationGroup_eq_of_valuationSubring_eqStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    {target' : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, y} L}
    [base.valuation.HasExtension target.valuation]
    [base.valuation.HasExtension target'.valuation]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (huniq' :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, y, y} base target')
    (hvaluationSubring :
      target.valuation.valuationSubring = target'.valuation.valuationSubring) (s : ℝ),
    lowerRamificationGroup (base := base) (target := target) huniq s =
      lowerRamificationGroup (base := base) (target := target') huniq' s

def lowerRamificationFiltration_eq_of_valuationSubring_eqStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    {target' : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, y} L}
    [base.valuation.HasExtension target.valuation]
    [base.valuation.HasExtension target'.valuation]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (huniq' :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, y, y} base target')
    (hvaluationSubring :
      target.valuation.valuationSubring = target'.valuation.valuationSubring),
    lowerRamificationFiltrationOfUniqueExtension (base := base) (target := target) huniq =
      lowerRamificationFiltrationOfUniqueExtension (base := base) (target := target') huniq'

def herbrandFunction_eq_of_valuationSubring_eqStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    {target' : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, y} L}
    [base.valuation.HasExtension target.valuation]
    [base.valuation.HasExtension target'.valuation]
    [FiniteDimensional K L]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (huniq' :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, y, y} base target')
    (hvaluationSubring :
      target.valuation.valuationSubring = target'.valuation.valuationSubring),
    herbrandFunctionOfUniqueExtension (base := base) (target := target) huniq =
      herbrandFunctionOfUniqueExtension (base := base) (target := target') huniq'

def inverseHerbrandFunction_eq_of_valuationSubring_eqStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    {target' : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, y} L}
    [base.valuation.HasExtension target.valuation]
    [base.valuation.HasExtension target'.valuation]
    [FiniteDimensional K L]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (huniq' :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, y, y} base target')
    (hvaluationSubring :
      target.valuation.valuationSubring = target'.valuation.valuationSubring),
    inverseHerbrandFunctionOfUniqueExtension (base := base) (target := target) huniq =
      inverseHerbrandFunctionOfUniqueExtension (base := base) (target := target') huniq'

def upperRamificationGroup_eq_of_valuationSubring_eqStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    {target' : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, y} L}
    [base.valuation.HasExtension target.valuation]
    [base.valuation.HasExtension target'.valuation]
    [FiniteDimensional K L]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (huniq' :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, y, y} base target')
    (hvaluationSubring :
      target.valuation.valuationSubring = target'.valuation.valuationSubring) (t : ℝ),
    upperRamificationGroupOfUniqueExtension (base := base) (target := target) huniq t =
      upperRamificationGroupOfUniqueExtension (base := base) (target := target') huniq' t


end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
