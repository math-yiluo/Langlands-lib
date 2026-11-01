# Block Weyl subgroups and interior cuts

Author: Worker 320.

`Langlands.Geometric.BlockWeylCutStatement` is a proposition about the
Library's actual ordered positive `BlockShape n`. It has two clauses,
each quantified over every natural rank.

The first clause fixes `i : Fin (n - 1)` and swaps standard coordinates
`i.val` and `i.val + 1` in `Fin n`. This transposition belongs to
`blockWeyl B` if and only if `i` is absent from `B.cuts`. The existing
cut convention places cut `i` at boundary position `i.val + 1`, between
these two coordinates. Thus an adjacent swap preserves every block
exactly when both coordinates lie inside one block.

The second clause says
`blockWeyl K ≤ blockWeyl B ↔ B.cuts ⊆ K.cuts`.
The orientation is deliberate: adding cuts refines blocks and reduces
the group of permutations preserving them. The two subgroups are the
actual subgroups of `Equiv.Perm (Fin n)` from `WeylDefinitions`, and the
subset relation compares the actual finite cut sets from `BlockShapeCuts`.
There is no assumed refinement map, abstract Coxeter group, or chosen
subgroup correspondence.

At ranks zero and one the type of interior edges is empty, so the first
clause is vacuous. In each of those ranks the unique positive ordered
block shape has an empty cut set and its Weyl subgroup is the trivial
permutation group, consistently with the second clause. No positive-rank
hypothesis or exceptional case is removed from the statement.

This is a derived finite combinatorial interface between existing
definitions. Its intended justification is the consecutive coordinate
numbering of positive blocks and the cumulative boundaries of their
associated composition; it translates no external literature theorem.
This module states the interface and proves neither clause. In
particular it supplies no alternating coefficient identity, geometric
lemma, representation-theoretic duality, or segment classification.
