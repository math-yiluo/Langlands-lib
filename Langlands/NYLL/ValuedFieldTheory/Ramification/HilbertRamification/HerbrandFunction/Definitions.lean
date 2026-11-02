/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1199, 2026-11-02, with source/interface extraction and
reuse analysis contributed by Worker 106:
isolate M305.004, M305.005 and M305.012 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix namespaces with
Langlands.NYLL, and import the focused generic inverse and published
actual lower filtration. Omit unused finite-dimensionality and the local
Fintype instance, retain four independent universes and supplied data,
and correct the forward-function docstring's absent residue hypothesis.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.InverseDefinition
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.LowerFiltration

/-!
# Herbrand functions and upper ramification groups for a unique valuation extension

This extracts exactly M305.004, M305.005 and M305.012 from the pinned NYLL
`HilbertRamification/HerbrandFunction.lean`. These are data definitions
on the supplied valuations, without finite-dimensionality or completeness.
-/

noncomputable section

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

/-- The Herbrand-function sum formula attached to the actual lower groups
under the stated unique-extension hypothesis. -/
noncomputable def herbrandFunctionOfUniqueExtension
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target) (s : ℝ) : ℝ :=
  Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction
    (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq) s

/-- The inverse Herbrand function in the general-DVF setting. -/
noncomputable def inverseHerbrandFunctionOfUniqueExtension
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target) (t : ℝ) : ℝ :=
  Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.inverseHerbrandFunction
    (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq) t

/-- The upper ramification group defined through the inverse Herbrand function
under the noncomplete standing assumptions: `G^t = G_{psi(t)}`. -/
def upperRamificationGroupOfUniqueExtension
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target) (t : ℝ) : Subgroup Gal(L/K) :=
  lowerRamificationGroup
    (base := base) (target := target) huniq
    (inverseHerbrandFunctionOfUniqueExtension
      (base := base) (target := target) huniq t)

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
