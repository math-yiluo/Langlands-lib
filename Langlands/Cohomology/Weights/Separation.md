# Algebraic weight separation

Author: Worker 41. This is a proposition-definition contribution for task
`8dc52f5f-7184-4bf3-b9a6-ffec96c1e83c`, revision 1.
Proof-status correction: Worker 333.

The paired Lean file defines an actual proposition over number fields,
polynomials, and their fraction fields. It isolates the algebraic implication
used in Kottwitz's Section 6. It is not the full Kottwitz theorem: it assumes
the polynomial trace identity and purity as hypotheses of an implication and
does not claim that any cohomology or automorphic object realizes those inputs.
This file defines the proposition, rather than an axiom or a proof. The
companion [SeparationProof](SeparationProof.md) proves that proposition.

Let \(L\) be a number field, \(d\) a natural number, \(q>1\) a natural number,
and \(w,a\) integers, and fix an embedding \(\iota:L\to\mathbf C\).
Let \(P\in L[X]\) be monic of positive degree.
For each \(0\le i\le 2d\), let \(H_i\in\mathbf C[X]\) be monic with all roots
Weil numbers of weight \(i+w\). Here the weight condition includes algebraicity
and all complex conjugates, as defined in the polynomial prerequisite.
Assume the following identity in the genuine rational function field \(\mathbf C(X)\):

\[
  \prod_{i=0}^{2d} H_i(X)^{(-1)^i}=(\iota P)(X)^a.
\]

`alternatingPolynomial` constructs the left side with the actual polynomial
embedding into `RatFunc ℂ`. The signed exponents are integers. Monicity in
the hypotheses makes every embedded polynomial nonzero, including when
inverted. No virtual representation is treated as a genuine vector space.
The positive degree assumption on \(P\) is essential to the nonvanishing
equivalence.

`WeightSeparationStatement` asserts that \(a\ne0\) if and only if some \(H_i\)
has positive degree. If \(a\ne0\), it also asserts that there is exactly one
family \(Q_i\in L[X]\) with:

- \(\prod_i Q_i=P\);
- every \(Q_i\) monic and pure of weight \(i+w\);
- \(H_i=(\iota Q_i)^{|a|}\);
- \(Q_i=1\) whenever \((-1)^i a<0\).

`IsWeightSeparation` expands these four properties as a conjunction, rather
than storing them as assumed fields of a cohomological object. The existential
quantifier lies in the conclusion. For positive \(a\), the last condition
removes odd degrees; for negative \(a\), it removes even degrees. Zero
cohomological summands are represented by characteristic polynomial \(1\).
The unique factors are over \(L\), so descent from complex factorization is
part of the conclusion established by the companion proof.

## Original source and conventions

Robert E. Kottwitz, *On the lambda-adic representations associated to some
simple Shimura varieties*, Inventiones Mathematicae 108 (1992), 653–665.
Literature ID: `kottwitz-1992-lambda-adic-simple-shimura`.
SHA-256:
`749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.

Exact locators: Theorem 1, p. 657; equation (5.6), p. 663; Section 6,
equation (6.1) and the ensuing factorization, p. 664.
Worker 41 read the complete original and visually checked pp. 657 and 664.
This proposition extracts the algebraic argument, with the positive-degree
hypothesis made explicit. In its intended application,
\(d=\dim S_K\), \(w=w(\xi)\), \(a=a(\pi_f)\),
\(P=P(\pi_p,E_v)\), and \(H_i\) is a complex realization of the characteristic
polynomial on \(W^i(\pi_f)_\lambda\). Its coefficients are not assumed to
descend to \(L\) in the hypotheses. The source's characteristic polynomials
use geometric Frobenius.
This polynomial statement has no Frobenius object or normalization choice
of its own and cannot establish that identification.

## Dependency and proof boundary

The imported project module is
`Langlands.Cohomology.Weights.Polynomial`, accepted artifact
`f1e2d792-01c3-4385-9bf4-4ae9c9e5464f`, version 1,
published in Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`, effective integrated snapshot
`42106411fcd47bace4b6e12d64b234b7564303775ee7b633bd3341e60208dd4b`,
Lean SHA-256
`47a03391e9b60f456f2b30133179940bb3fa75ee2b8c740b03641aaa0742964f`.
Machine validation, independent semantic review by Reviewer 124, and publication
have passed. Integration `ce5a00e3f0724675ad6e9ae202fe5cf7` retains exactly these
Lean bytes and paired Markdown SHA256
`0d2b84fde43d92f8476a81d37d4725c91a7f347a77ae88629704307846513a6b`.
The current-Library check reports no missing or changed file and no unavailable
dependency.

The only other dependency is the pinned Mathlib environment
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

The independently accepted and published theorem
[`Langlands.Cohomology.Weights.weightSeparationStatement`](SeparationProof.lean#L129)
in `Langlands.Cohomology.Weights.SeparationProof` proves exactly
`WeightSeparationStatement.{u}`. It proves the nonvanishing equivalence and,
when \(a\ne0\), existence and uniqueness of the factors over \(L\), including
their purity, multiplicity identities and wrong-parity factors equal to \(1\).
Its signed rational-function argument gives the root-multiplicity identity;
distinct weights give root coverage and the purity hypothesis needed for the
coefficient-field factors. Descent, multiplicities and algebraic parity are
therefore established, not pending obligations.

This proof retains \(q>1\), monicity, positive degree of \(P\), root purity,
and the rational-function identity as hypotheses. It supplies no geometric
trace identity or cohomological purity theorem. No cohomological,
compatible-family, Hodge–Tate, automorphic transfer, representation-theoretic
parity-removal, or ramified compatibility theorem is proved or assumed as an
axiom here. The complete Kottwitz/Harris results require further global and
geometric inputs beyond this algebraic proposition.
