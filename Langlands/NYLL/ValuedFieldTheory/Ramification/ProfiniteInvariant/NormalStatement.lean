/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 179, 2026-11-10: extract the statement of M242.001,
`RamificationTheory.Ideal.Quotient.normal_of_profinite` (original lines 26–101,
theorem at line 45), at upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 into one closed Prop-valued
definition; prefix the namespace with Langlands.NYLL; name the three
independent source universes u, v, w; bind the unchanged variable telescope of
lines 28–32, with its binder kinds, inside the Prop, so that G is quantified
there instead of through `include G`; keep `Ideal.Quotient.field` a local
instance. The original imports are unchanged. The original proof, the
`noncomputable section` and `open scoped Pointwise` are omitted.
Retained license and notices: licenses/NYLL/.
-/

import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Invariant.Profinite

/-!
# Profinite invariant rings: normality on maximal residue fields

The closed statement of NYLL M242.001: for a compact totally disconnected
topological group acting continuously on a discrete ring `B` whose invariants
are `A`, the residue field extension at maximal ideals `Q` over `P` is normal.
-/

universe u v w

namespace Langlands.NYLL.RamificationTheory.Ideal.Quotient

attribute [local instance] Ideal.Quotient.field

/-- Profinite version of `Ideal.Quotient.normal`: if a compact totally
disconnected topological group `G` acts continuously on the discrete ring `B`
by `A`-algebra automorphisms with invariant ring `A`, then for maximal ideals
`Q` of `B` and `P` of `A` with `Q` lying over `P`, the residue field extension
`(B ⧸ Q) / (A ⧸ P)` is normal. -/
def normal_of_profiniteStatement : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {G : Type w} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B]
    [ContinuousSMul G B] [Algebra.IsInvariant A B G]
    (P : Ideal A) (Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P],
    Normal (A ⧸ P) (B ⧸ Q)

end Langlands.NYLL.RamificationTheory.Ideal.Quotient
