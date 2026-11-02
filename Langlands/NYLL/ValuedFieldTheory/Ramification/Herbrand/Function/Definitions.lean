/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.RamificationQuotients.Filtration
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Normalized Herbrand functions of a normal subgroup filtration

Adapted from NYLL `Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`,
commit fbd320cd8b1b06487c58227e92eb135794267709, lines 48–53 and 112–119
(M303.003, M303.004 and M303.013).
Worker 60 extracted exactly these definitions, prefixed the namespace by
`Langlands.NYLL`, and reduced the imports to the published generic filtration
and Mathlib cardinality, finite sums and real natural floor.
The unused ambient `[Finite G]`, local subgroup instances, noncomputable section
and intervening theorems are omitted; the definition bodies are unchanged.
Big-operator notation is opened explicitly.
Worker 106 supplied the source extraction, inferred-interface and reuse analysis.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.RamificationTheory.DiscreteValuationField
namespace AntitoneNormalSubgroupFiltration

open scoped BigOperators

variable {G : Type u} [Group G]
variable (F : AntitoneNormalSubgroupFiltration G)

/-- The slope of the Herbrand function on `(i,i+1)`.  This is the shifted
quantity `|G_(i+1)| / |G_0|`, not the pre-existing `herbrandStep i`. -/
noncomputable def herbrandSlope (i : ℕ) : ℝ :=
  (Nat.card (F.lower (i + 1)) : ℝ) / Nat.card (F.lower 0)

/-- The value of the normalized Herbrand function at a natural number. -/
noncomputable def herbrandValueNat (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (herbrandSlope F) i

/-- The Herbrand-function sum formula, in its explicit piecewise-linear form. -/
noncomputable def herbrandFunction (s : ℝ) : ℝ :=
  if 0 ≤ s then
    let m := ⌊s⌋₊
    (herbrandValueNat F) m +
      (s - (m : ℝ)) * (herbrandSlope F) m
  else
    s

end AntitoneNormalSubgroupFiltration
end Langlands.NYLL.RamificationTheory.DiscreteValuationField
