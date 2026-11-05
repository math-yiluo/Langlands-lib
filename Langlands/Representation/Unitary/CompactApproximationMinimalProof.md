# Proof of minimal closed invariant subspaces

Worker 116 implements the internal minimal-subrepresentation step motivated
by Getz–Hahn Lemma 9.3.1, printed p.247, one-based PDF p.259.

The proof first obtains a nonzero intersection with a nonzero eigenspace
F of one compact symmetric approximating operator. F is finite-dimensional.
It minimizes the natural-number dimension of U intersected with F over
closed invariant U contained in W whose intersection is nonzero. The
original W makes this collection nonempty.

A nonzero x in a minimizing intersection generates P, the topological
closure of the complex span of its actual π-orbit. Continuity of every
bounded operator π(g) and the homomorphism laws show P is invariant.
Closure and span minimality put P in every closed invariant space
containing x, in particular U and W. Membership of x makes P nonzero.

For closed invariant Q contained in P, unitarity and the inverse group
action make Q's orthogonal complement invariant. Symmetry of the chosen
T(n) and preservation of Q show that its orthogonal projection commutes
with T(n). The projection of x therefore belongs to F.

If that projection is zero, x belongs to Q's invariant orthogonal
complement. The cyclic minimality of P puts P in that complement, hence
Q is zero. If the projection is nonzero, Q intersected with F is nonzero.
The dimension-minimizing property and inclusion in U intersected with F
make the two intersections equal. Thus x belongs to Q, and cyclic
minimality gives Q = P.

The proof uses the actual submodules and orthogonal projection, not a
supplied decomposition or irreducible-existence hypothesis. It imports
the published eigenspace proof. The statement's Markdown records exact
original-source and errata provenance and the remaining decomposition,
multiplicity and automorphic obligations.
