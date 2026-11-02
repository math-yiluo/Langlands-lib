/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1199, 2026-11-01, with source extraction, exact telescope
and closed statement design contributed by Worker 106:
extract the conclusion of M305.002 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 into one closed Prop target.
Prefix namespaces with Langlands.NYLL, import the published actual lower
filtration, and move all mathematical binders inside the Prop.
Retain four independent universes and comparison universe x.
The source proof, theorem name and simp attribute are reserved for later work.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.LowerFiltration

/-!
# Natural-level projection of the actual lower filtration: statement

This closed proposition states the conclusion of M305.002, lines 55–63 of
the pinned NYLL `HerbrandFunction.lean`, with the original supplied data.
-/

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

/-- At every natural index, the actual lower filtration projects to the
real lower group for the same supplied unique valuation extension. -/
def LowerRamificationFiltrationProjectionStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (n : ℕ),
    (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq).lower n =
      lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ)

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
