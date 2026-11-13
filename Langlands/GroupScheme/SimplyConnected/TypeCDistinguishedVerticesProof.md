# The distinguished vertices of a type C antihermitian group

`typeCDistinguishedVertices` proves exactly the Library proposition
`TypeCDistinguishedVerticesStatement`, at an arbitrary universe parameter.
All hypotheses of that statement are retained, including arbitrary fields,
the actual index and its Cartan numbering, the trace-valued antihermitian
condition, and the natural Witt index.

The Witt-torus splitting theorem supplies a maximal split torus of the
antihermitian group, a symplectic splitting over the separable closure, its
repeated-block image, and the bound `wittIndex * degree ≤ n`. The given group
isomorphism transports this torus and splitting to the group in the statement.
The block-torus adapter constructs compatible actual Tits index data and
computes every numbered simple-root restriction in integer coordinates.

The restriction is nonzero precisely at the positions `degree, 2 * degree,
..., wittIndex * degree`. Actual-index independence transports this marked set
to the supplied index. Rigidity of the oriented type C Cartan matrix for
`n ≥ 2` preserves the exact supplied numbering, so the result concerns each
original vertex. The proof uses semisimplicity from the supplied index;
the simply connected and absolutely almost simple assumptions need no
additional use.

This proof composes the Library's torus, pinning, root-restriction and
index-comparison results. It assumes no classification of type C forms,
rank-one groups, or Kneser–Tits result.
