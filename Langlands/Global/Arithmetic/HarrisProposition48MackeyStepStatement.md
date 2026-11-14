# A compatible arithmetic step in the Proposition 4.8 induction

`Langlands.Global.Harris.Proposition48MackeyStepStatement` is an unproved
arithmetic input. For a one-place valid problem of rank greater than
one, it chooses an intermediate field `D` such that `D/E` is Galois,
cyclic and of prime degree. The actual double-coset index has cardinality
either one or `[D:E]`. For every automorphism representative `a` of the
parent's normal closure, the same choice of `D` admits an actual child
problem `R` for `D·a(E')/D`.

The child relation requires commuting field isomorphisms and an embedding
of the child's closure into the parent's closure, the same quadratic
subfield image, and exactly the raw norm-pulled character
`a(ξ) ∘ N_{D·a(E')/a(E')}` transported through the actual source-field
isomorphism. The auxiliary place lies above the parent's auxiliary
place. The unused primary data impose no further inheritance condition.
The relation is on representatives; no descent of choices to double
cosets is asserted.

Each child satisfies `IsAuxiliaryValidAtParity ([E':E] - 1)`, including
relative regularity, conjugate inversion and local general position,
the source's conditions (i), (ii) and (iii). Its rank is exactly
`mackeyRank D a = [D·a(E'):D]`. Its own normal-closure degree is strictly
smaller than `[L:E]`, the induction measure. This strict inequality is
separate from any rank comparison. Correcting the child's infinity
parity is the obligation of the separate auxiliary normalization
statement; this arithmetic input makes no automorphic existence claim.

The quantifier order is essential: a compatible `D` and all its children
are chosen together. General position supplies an appropriate local
tower and its subfields. The statement does not require inheritance for
every intermediate field of the closure. Likewise it does not require
two independently specified completion identifications to agree along
that tower. The one-place induction is sufficient because the original
full validity implies auxiliary validity and the output predicates
already refer only to the auxiliary place.

Source: M. Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p*, Invent. Math. 134 (1998), 177–210,
`harris-1998-local-langlands`, Proposition 4.8 proof, printed p.202
(`math_9611226v1.tex`, lines 1574–1614) for the compatible field tower,
Mackey characters, smaller closure degree and conditions (i)–(iii);
pp.202–203 (lines 1630–1648) for the prime cyclic final step and the
one-or-prime cardinality dichotomy. The constituent degree convention
is the degree of its inducing extension, as required by the rank-one
base case, rather than the inconsistent rank expression in the printed
Lemma 4.7 proof on pp.204–206.

This is a derived single-step packaging of that induction, with the
one-place scope and explicit inherited infinity parity explained above.
It is not a proof of inheritance or of Proposition 4.8. No `n < p`
hypothesis is added. The existing declarations and signatures remain
unchanged.
