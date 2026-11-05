# Proof of a dense orthogonal minimal family

Worker 116 implements the orthogonal-family step motivated by
Getz–Hahn Lemma 9.3.1, printed p.247, one-based PDF p.259.
The statement Markdown records exact original-source and errata provenance.

The proof orders sets of actual minimal nonzero closed invariant
submodules contained in W. Valid sets have pairwise orthogonal members.
The union of a chain is valid: every member comes from a chain element,
and any two members occur together in one of two comparable elements.
The empty chain has the empty union. Zorn's lemma gives a maximal valid
set A.

Let R be its algebraic supremum and K the topological closure of R.
Every member lies in W, so closure minimality puts K in W.
Invariance of each member puts R in the preimage of K under every
π(g); that preimage is closed because π(g) is bounded.
Closure minimality therefore proves invariance of K.

If K differs from W, orthogonal projection onto K decomposes W as
K plus K-perp intersected with W, so that relative orthogonal complement
is nonzero. It is closed. Invertibility and inner-product preservation
of π show K-perp is invariant; intersecting with W preserves invariance.
The preceding compact-approximation minimality theorem supplies an
actual nonzero minimal closed invariant P in this complement.

P is orthogonal to K and thus to every member of A.
It cannot already belong to A: it would lie in K and K-perp, forcing
P to be zero. Inserting P gives a larger valid set, contrary to
maximality. Thus K = W, as required.

The theorem proves the exact published proposition
`Langlands.Analysis.CompactApproximationOrthogonalStatement`.
The group and Hilbert space have independent universes. The space is any
complete complex inner-product space, and the actual bounded complex-linear
group action preserves the inner product. The supplied compact symmetric
operators converge strongly to the identity and preserve every closed
invariant complex submodule. Every closed invariant W is allowed, including
W = 0, when the family must be empty. No separability, countability or
supplied decomposition hypothesis is added.

This is an existence and dense-span proof. It imports the published
minimality theorem, whose eigenspace prerequisite is also published.
The statement Markdown records the original-source and errata provenance.
An isometric equivariant map from an actual Hilbert direct sum, finite
representation multiplicity, Dirac weights, integrated operators and
concrete automorphic realization remain separate obligations.
