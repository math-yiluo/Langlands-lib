# Rigidity of strictly decreasing block parameters

Author: Worker 385.

`Langlands.Exponents.blockParameterPermutationRigidity` proves exactly the
published closed proposition
`Langlands.Exponents.BlockParameterPermutationRigidityStatement`. The proof
imports its statement module unchanged.

## Implemented argument

Fix a rank `n`, block shapes `B,C`, strictly decreasing real block functions
`t,s`, and the assumed coordinate permutation `w`. Positivity of `B.size i`
provides the coordinate `B.index i 0` of every source block. Define `f i` as
the target block containing its image under `w`. The assumed coordinate
equality and `Geometric.blockIndex_index` give `t i = s (f i)`.

The inverse permutation gives a map `g` in the other direction with
`s j = t (g j)`. Strict decrease implies injectivity of both parameter
functions, so these value identities prove `g (f i) = i` and
`f (g j) = j`. They define an equivalence `e` of block indices. The two
instances of `StrictAnti.le_iff_ge` show
`f i ≤ f j ↔ s (f j) ≤ s (f i) ↔ t j ≤ t i ↔ i ≤ j`.
Thus the same equivalence defines the order isomorphism `b`.

For each source block `i`, the original coordinate equality and injectivity
of `s,t` give the biconditional
`blockIndex B a = i ↔ blockIndex C (w a) = f i`.
Consequently `w.subtypeEquiv` restricts `w` to an equivalence of those coordinate
fibers. Each fiber is identified with the finite coordinate type of its block
by `BlockShape.indexEquiv.symm.subtypeEquiv`, followed by
`Equiv.sigmaSubtype`. Composing these equivalences yields
`Fin (B.size i) ≃ Fin (C.size (f i))`. Applying `Fintype.card_congr` recovers
the required equality of block sizes. The previously established identity
`t i = s (f i)` gives the value component of the conclusion.

All representative coordinates are chosen only after a block index is supplied.
The constructions therefore work for empty index types, including rank zero,
without a positive-rank premise or a separate case split. One-block shapes and
arbitrary real parameter values are included. In particular the proof imposes
no positivity, central normalization, or zero-sum condition on `t,s`.

## Internal provenance and scope

This is an internally derived finite-order and counting proof. Its coordinate
fiber equivalences use the existing block-coordinate definitions and Mathlib's
equivalence and finite-cardinality constructions. The same standard fiber
identification appears in the published
`Langlands.CuspidalSupport.TotalConjugatingCount.card_blockIndex_fiber`;
the present proof constructs the needed composite equivalence locally and
does not introduce a duplicate public counting lemma.

The statement module records the motivating application to the final chamber
rigidity step in A. J. Silberger, *The Langlands quotient theorem for p-adic
groups* (1978), Proposition 6.1, printed pp.102–103. This exact finite-coordinate
lemma is internal and is not attributed as a theorem stated by Silberger.
The proof uses only the coordinate permutation supplied in the proposition.
It supplies no representation-theoretic Weyl comparison, quotient uniqueness,
analytic continuation, head theorem, or square-integrable classification.
