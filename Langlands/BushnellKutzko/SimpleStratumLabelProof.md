# Labels of simple strata in a principal order: proof

`Langlands.BushnellKutzko.simpleStratumLabel` proves
`SimpleStratumLabelStatement` at independent universes `uF` (base field)
and `uV` (vector space). This is the upper-bound direction of BK94 (1.14)
for a principal hereditary order: the simple strata \([\mathfrak A,n,m,\beta]\)
on a fixed principal lattice chain admit a map \(\rho\) to the label set
\(P^m_n(e(\mathfrak A),N/e(\mathfrak A);q_F)\) such that equal labels give
\(U(\mathfrak A)\)-conjugacy up to equivalence, \(d(\rho(\beta))=f(F[\beta]\mid F)\)
and \(e(F[\beta]\mid F)\,e(\rho(\beta))=e(\mathfrak A)\).

## Proof

The proof is one application of `simpleStratumLabel_of`
([SimpleStratumLabelReduction](SimpleStratumLabelReduction.md)), which
derives the statement by induction on \(n-m\) from three hypotheses. They
are discharged by published proofs:

- `PureStratumSimpleApproximationStatement.{uF, uV}` (BK93 (2.4.1)(i)) by
  `pureStratumSimpleApproximation`; it supplies the restriction of a simple
  stratum at level \(m\) to a simple stratum at level \(m+1\).
- `MinimalSimpleStratumPolynomialStatement.{uF, uV}` (BK94 (1.4)–(1.5)) by
  `minimalSimpleStratumPolynomial`; it labels the simple strata at depth
  \(n-1\) over \(F\), the base of the induction.
- `MinimalSimpleStratumPolynomialStatement.{uV, uV}`, the same theorem at the
  universe of \(V\); it labels the derived strata over the generated fields
  \(E=F[\gamma]\subseteq\operatorname{End}_F(V)\), which lie in that universe,
  in the induction step.

The inductive construction, the conjugacy argument for equal labels and the
computation of the invariants are described in the Markdown of the modules
`SimpleStratumLabelReduction`, `SimpleStratumLabelStep`,
`SimpleStratumLabelFibre` and the modules they import.

Only the injectivity of the label map up to conjugacy and the invariant
formulas are proved, as the statement asks; the bijectivity in BK94 (1.14)
is not part of `SimpleStratumLabelStatement`.

Source. C. J. Bushnell and P. C. Kutzko, *Simple types in GL(N): computing
conjugacy classes*, Contemp. Math. 177 (1994), 107–135, (1.14), printed
pp. 116–117 (PDF pp. 129–130); registered as
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact
open subgroups*, Annals of Mathematics Studies 129 (1993), (2.4.1)(i),
printed p. 65 (PDF p. 77); registered as
`bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
