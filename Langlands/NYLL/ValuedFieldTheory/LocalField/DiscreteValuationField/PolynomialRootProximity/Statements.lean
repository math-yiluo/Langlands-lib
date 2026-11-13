/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 325, 13 November 2026: extract the two theorem types from
upstream fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued definitions;
qualify public names with Langlands.NYLL, give the private helper its planned
PortInternal name, and quantify all source binders inside the propositions.
The implicit source universe of the multiset element type is named v,
independently of the ring universe u. Proofs are omitted and the proof-only
Mathlib.Data.Finset.Max import is removed. See the paired Markdown.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.DiscreteValuationRing.Basic

open scoped Polynomial

namespace Langlands.NYLL.PortInternal.M395

/-- Statement target for the private multiset comparison, source unit M395.001. -/
def d001Statement.{u, v} : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {α : Type v} (s : Multiset α) (f g : α → R)
    (h : ∀ z ∈ s,
      IsDiscreteValuationRing.addVal R (f z) ≤
        IsDiscreteValuationRing.addVal R (g z)),
    IsDiscreteValuationRing.addVal R ((s.map f).prod) ≤
      IsDiscreteValuationRing.addVal R ((s.map g).prod)

end Langlands.NYLL.PortInternal.M395

namespace Langlands.NYLL.Polynomial.Splits

/-- Statement target for the DVR root-proximity estimate, source unit M395.002. -/
def exists_root_addVal_eval_le_sub_add_derivativeStatement.{u} : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (p : R[X]) (hs : p.Splits) (hm : p.Monic)
    (hdeg : p.natDegree ≠ 0) (x : R),
    ∃ y, y ∈ p.roots ∧
      IsDiscreteValuationRing.addVal R (p.eval x) ≤
        IsDiscreteValuationRing.addVal R (x - y) +
          IsDiscreteValuationRing.addVal R (p.derivative.eval y)

end Langlands.NYLL.Polynomial.Splits
