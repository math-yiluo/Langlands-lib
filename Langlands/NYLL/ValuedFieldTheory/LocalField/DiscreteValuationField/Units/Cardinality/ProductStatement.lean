/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.GradedPiece

/-!
# Iterated subquotient cardinality as a product of graded pieces

Adapted by Worker 299 and Worker 475 from NYLL M120.074 at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Modifications: add the
`Langlands.NYLL` namespace prefix; extract the proposition as a `Prop`-valued
definition with suffix `Statement`; rename its unused hypothesis `_hN`; and
import the published shared filtration, subquotient and graded-piece data.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

open scoped BigOperators

namespace DiscreteValuationField.AntitoneSubgroupFiltration

/-- Source M120.074: the cardinality of the iterated subquotient `U^l/U^(l+r)`
is the product of the cardinalities of the `r` adjacent graded pieces
`U^(l+i)/U^(l+i+1)`. -/
def card_principalUnitSubquotient_eq_prod_gradedPieceStatement
    {G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)
    (_hN : ∀ i : ℕ, (U.principalUnitSubgroup i).Normal)
    [∀ i j : ℕ, Finite (U.principalUnitSubquotient i j)]
    (l r : ℕ) : Prop :=
  Nat.card (U.principalUnitSubquotient l (l + r)) =
    ∏ i ∈ Finset.range r,
      Nat.card (U.principalUnitGradedPiece (l + i))

end DiscreteValuationField.AntitoneSubgroupFiltration

end Langlands.NYLL.LocalFieldTheory
