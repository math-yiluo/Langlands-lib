# Conrad's Example 5.13: proof

Author: Worker 105.

`henselianExtensionPointNotClosed` proves the published statement
`Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianExtensionPointNotClosedStatement.{u}`.
That statement is Example 5.13 of Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (2011), printed p.20. The proof uses only the standard axioms.

## The statement

Let:

- `K` be a nontrivially normed, ultrametric, complete field;
- `K'` be a nontrivially normed `K`-algebra with `finrank K K' = 2` and `K'/K` separable.

Then there is an algebraic space `X` over `Spec K` such that:

1. `X` is quasi-separated and locally of finite type;
2. its diagonal is representable with every represented projection an affine immersion;
3. the image of `X(K) → X_{K'}(K')` is not closed for the étale-chart topology over `K'`.

## Proof

- `K'` is finite-dimensional over `K`, and `QuadraticConj.nonempty` provides the conjugation
  data `D`.
- `X` is the Galois-twisted line `GaloisTwistedLine.space D`. It is Conrad's `L'/G`: the affine
  `K'`-line modulo the étale group obtained from `(Z/2Z)_L` by deleting the non-identity point
  over the origin (`GaloisTwistedLineRing`, `GaloisTwistedLineRelation`,
  `GaloisTwistedLineQuotient`).
- Clause (1) is `isQuasiSeparated D` and `locallyOfFiniteTypeOverBase D`.
- Clause (2) is `relative_diag D` (`GaloisTwistedLineDiagonal`).
- Clause (3) is `not_isClosed_range D` (`GaloisTwistedLineTopology`).

The ultrametric and completeness hypotheses of the statement are not used. The construction and
the non-closedness argument work for any nontrivially normed extension of degree two with a
conjugation. Conrad states the example over a complete field to show that the closed-embedding
property of Proposition 5.11(3) fails even in that case. Separability is used: it makes
`K'/K` Galois, which provides the conjugation.
