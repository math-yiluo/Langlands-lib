# Open stabilizers of Schwartz–Bruhat row functions

`Langlands.HarmonicAnalysis.rowTestSmooth` proves
`RowTestSmoothStatement F n`, with exactly its topological-field hypotheses,
arbitrary field universe, and natural-number rank.

The implemented argument defines the subgroup of invertible matrices preserving
the test function on every row. Associativity of row multiplication proves
closure under products, and cancellation proves closure under inverses.

Local constancy of the test function and continuity of row multiplication make
the equality relation `Φ(xg) = Φ(x)` open in the product of the general linear
group and row space. This relation contains the identity times the topological
support. The generalized tube lemma, applied to the compact singleton and the
compact topological support, supplies a neighborhood of the identity on which
invariance holds uniformly on that support.

Intersect this neighborhood with its inverse image under inversion. For a
matrix in this intersection, a row in the support satisfies invariance
directly. If the row is outside the support and its translate is inside, apply
the inverse matrix to that translate and use cancellation. If both are outside,
both function values vanish. Thus the entire symmetric neighborhood lies in the
stabilizer. A subgroup containing an identity neighborhood is open.

Two direct consequences provide the compact-reduction interface.
`rowTranslate_locallyConstant` uses open cosets of the stabilizer to show local
constancy of the function-valued translate map. `finite_rowTranslate_range`
restricts it to any compact set of matrices and applies finiteness of the range
of a locally constant map on a compact space. Neither consequence requires a
topology on the function-valued codomain.

This is an elementary topological proof of the derived target, whose motivation
is the test-function portion of the compact-group finiteness reduction in
Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg Convolutions* (1983),
printed p. 391 before display (3). It proves no analytic continuation or
normalized-generator assertion.

Source: `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
printed p. 391.
