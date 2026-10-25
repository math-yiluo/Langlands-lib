# Topological comparison from an open integral subring

This is an internal construction extending the final-topology API in
`Langlands.Topology.Rationalization.Basic`. Its purpose is to upgrade a normalized
algebraic scalar comparison to a homeomorphism. It is not a new transcription
of a theorem from the literature.

Let `R` be a commutative ring with a topology, and let `B` be a commutative
topological ring and a rational algebra. Suppose given a rational algebra
equivalence

\[
e:\mathbb Q\otimes_{\mathbb Z}R \simeq_{\mathbb Q} B
\]

and a ring homomorphism `j : R →+* B` which is an open embedding. Require the
normalization

\[
e(q\otimes a)=\operatorname{algebraMap}(q)\,j(a)
\qquad(q\in\mathbb Q,\ a\in R).
\]

`comparisonHomeomorph e j hj he` has exactly the underlying equivalence `e`
and its inverse. Its source has `finalTopology R`: a subset is open precisely
when its preimage under every map `a ↦ q ⊗ a` is open in `R`. Its target has
the given topology of `B`. The two application lemmas identify both directions
with `e` and `e.symm`.

The proof of forward continuity uses the universal property of the final
topology. The composite with the `q` chart is multiplication by the fixed
element `algebraMap q` after the continuous map `j`.

For inverse continuity, `Langlands.Topology.Rationalization.exists_chart` from
[Lattice](Lattice.md) writes every element of the rationalization as `q ⊗ a`
for some nonzero rational `q`. This follows
from the localization description of rational scalar extension and does not
assume torsion freeness of `R`. Multiplication by `algebraMap q` on `B` is a
homeomorphism, with inverse multiplication by `algebraMap q⁻¹`; the proof uses
the ring laws and continuity of multiplication. Hence the map
`a ↦ e (q ⊗ a)` is an open embedding. Testing continuity of `e.symm` at a
point in that open image reduces to continuity of `a ↦ q ⊗ a`, which is part
of the final-topology construction.

No topology on the rational numbers, continuity of their diagonal map, or
nontriviality assumption on `B` is required. No continuity of ring operations
on `R` is assumed. The input equivalence, open embedding and normalization are
explicit hypotheses; this construction does not establish their existence.
