/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1199, 2026-11-01, with source/interface extraction and
actual lower-group proof routing contributed by Worker 106:
isolate M305.001 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix namespaces with
Langlands.NYLL, and replace the wholesale Herbrand-function import with
the published generic filtration and actual lower-group proof modules.
The four universes, supplied-data telescope and construction are retained.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.RamificationQuotients.Filtration
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.LowerGroupProof

/-!
# Integral lower ramification filtration of a unique valuation extension

M305.001 of the pinned NYLL `HerbrandFunction.lean`: the actual real lower
groups at natural indices, with their published normality and antitonicity.
-/

noncomputable section

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

/-- The integral levels of the real lower-ramification groups, packaged as a
`AntitoneNormalSubgroupFiltration`. This uses the supplied unique valuation
extension without a completeness hypothesis. -/
def lowerRamificationFiltrationOfUniqueExtension
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target) :
    Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration
      Gal(L/K) where
  lower n := lowerRamificationGroup
    (base := base) (target := target) huniq (n : ℝ)
  lower_normal n := lowerRamificationGroup_normal
    (base := base) (target := target) huniq (n : ℝ)
  antitone := by
    intro m n hmn
    apply lowerRamificationGroup_antitone
      (base := base) (target := target) huniq
    exact_mod_cast hmn

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
