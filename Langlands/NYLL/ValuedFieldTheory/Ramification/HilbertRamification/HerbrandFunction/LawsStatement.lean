/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 27, 2026-11-02, with source/interface analysis and
closed-target design contributed by Worker 106:
extract the eight conclusions M305.006-.011/.013-.014 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 into one closed Prop target.
Prefix namespaces with Langlands.NYLL, import the published actual
definitions, and move all supplied-data binders inside the proposition.
Retain four independent universes, unrestricted evaluation clauses and
the finite-dimensional scope of the later six laws.
Omit the source proofs, theorem attributes and local Fintype instance.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.Definitions

/-!
# Actual unique-extension Herbrand laws: statement

This closed proposition extracts M305.006-.011/.013-.014, lines 88-191
of the pinned NYLL `HilbertRamification/HerbrandFunction.lean`.
The two evaluation clauses are unrestricted; the following six laws
retain the source finite-dimensional hypothesis.
-/

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

/-- Evaluation, inverse, order and actual upper-group laws for the
Herbrand functions of the same supplied unique valuation extension.
Only the six-law block requires finite-dimensionality. -/
def UniqueExtensionHerbrandLawsStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target),
    (∀ s : ℝ,
      herbrandFunctionOfUniqueExtension (base := base) (target := target) huniq s =
        Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction
          (lowerRamificationFiltrationOfUniqueExtension
            (base := base) (target := target) huniq) s) ∧
    (∀ t : ℝ,
      inverseHerbrandFunctionOfUniqueExtension (base := base) (target := target) huniq t =
        Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.inverseHerbrandFunction
          (lowerRamificationFiltrationOfUniqueExtension
            (base := base) (target := target) huniq) t) ∧
    (∀ [FiniteDimensional K L],
      (∀ t : ℝ,
        herbrandFunctionOfUniqueExtension (base := base) (target := target) huniq
          (inverseHerbrandFunctionOfUniqueExtension
            (base := base) (target := target) huniq t) = t) ∧
      (∀ s : ℝ,
        inverseHerbrandFunctionOfUniqueExtension (base := base) (target := target) huniq
          (herbrandFunctionOfUniqueExtension
            (base := base) (target := target) huniq s) = s) ∧
      StrictMono (herbrandFunctionOfUniqueExtension (base := base) (target := target) huniq) ∧
      StrictMono (inverseHerbrandFunctionOfUniqueExtension (base := base) (target := target) huniq) ∧
      (∀ s : ℝ,
        upperRamificationGroupOfUniqueExtension (base := base) (target := target) huniq
          (herbrandFunctionOfUniqueExtension
            (base := base) (target := target) huniq s) =
          lowerRamificationGroup (base := base) (target := target) huniq s) ∧
      (∀ t : ℝ,
        (-1 : ℝ) ≤ inverseHerbrandFunctionOfUniqueExtension
          (base := base) (target := target) huniq t ↔ (-1 : ℝ) ≤ t))

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
