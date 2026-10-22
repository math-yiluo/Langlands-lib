# Proof of the topological lattice prerequisites

Author: Worker 57.

The target is `Langlands.Shimura.Coefficients.LatticeTopologyStatement`.
The proof follows the explicit hypotheses of that statement and does not
add a local-field specialization.

First, a private lemma shows that if `Lambda` is an open finitely generated
submodule and `S` is compact, then `Lambda + span_R(S)` is finitely generated.
Cover `S` by the open sets of points whose difference from a chosen point of
`S` belongs to `Lambda`. A finite subcover gives finitely many representatives
in `S`. Every point of `S` is their representative plus an element of `Lambda`,
so adding `span_R(S)` is the same as adding the span of those finitely many
representatives. Finite generation follows without a noetherian assumption.

Next choose finitely many generators of the initial lattice. Let `S` be the
union of their orbits. Each orbit is a continuous image of the compact group;
the finite union is compact. Span induction and linearity identify the
orbit span of the lattice with `Lambda + span_R(S)`. The first lemma therefore
proves its finite generation. The published `orbitSpan_isLattice` gives its
full span, and `orbitSpan_stable` gives stability. Containment of the open
initial lattice implies openness of the larger additive subgroup.
This is the theorem `compactLattice`.

For the congruence kernel, choose finitely many generators of the integral
module. The kernel is the intersection, over these generators `x`, of the
conditions `rho(g)x - x ∈ I^n M`. One direction follows by evaluating the
trivial action modulo `I^n`. In the other direction, `LinearMap.ext_on`
compares the quotient map composed with the action to the quotient map itself;
equality on the generating set implies equality everywhere. The quotient
representative criterion then gives membership in the kernel.

Each condition is open by continuity of the orbit map and subtraction and
openness of `I^n M`. Their finite intersection is open. Mathlib's
`Subgroup.quotient_finite_of_isOpen` proves the quotient finite: the quotient
of a compact group by an open subgroup has compact discrete topology.
This gives `congruenceKernelTopology`.

Finally `latticeTopology` pairs these two conclusions. These are direct
formal proofs of the published target; they do not rely on any claims of
scheme representability, coefficient descent, or finite-field descent.
