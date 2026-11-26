# Labels for simple strata in a principal order

`Langlands.BushnellKutzko.SimpleStratumLabelStatement` states the
upper-bound direction of BK94 (1.14) for a principal hereditary order.
Let \(F\) be a nonarchimedean local field, let \(V\) have finite dimension
\(N\geq 1\) over \(F\), and let \(L\) be a principal lattice chain
presenting \(\mathfrak A\). For integers \(0\leq m<n\), the proposition
asserts the existence of a function \(\rho\) on the simple strata
\([\mathfrak A,n,m,\beta]\) represented on \(L\), with values in
\(P^m_n(e(\mathfrak A),N/e(\mathfrak A);q_F)\).

The codomain is the subtype of `labelSet` from [Labels](Labels.md).
The level arguments use `m.toNat` and `n.toNat`, which give the original
levels under the inequalities. The parameter `Nat.card 𝓀[F]` is the
residue-field cardinality \(q_F\). In the principal case, the common
layer dimension is \(d(\mathfrak A)=N/e(\mathfrak A)\) and its least
positive period is \(p(\mathfrak A)=1\). Thus the normalized indices
\(m',n'\) of (1.14) are \(m,n\) and \(e(\mathfrak A)/p(\mathfrak A)\)
is `L.period`.

If two strata have the same label, there is \(u\in U(\mathfrak A)\)
such that \(u^{-1}\beta_1u\) belongs to the second stratum's coset.
At the fixed order and depth this is equivalence of the conjugated
first stratum with the second. The two invariant clauses say
\(d(\rho(\beta))=f(F[\beta]\mid F)\) and
\(e(F[\beta]\mid F)e(\rho(\beta))=e(\mathfrak A)\), using
`Label.d`, `Label.e` and the Library's generated-field invariants.

The printed display in (1.14) includes both formulas. The ramification
formula uses (1.5) at depth \(n-1\). In the restriction step, (1.12)
multiplies the ramification index of \(F[\gamma]\) by that of the
derived extension over \(F[\gamma]\). For a simple derived stratum,
(1.5) gives the latter factor as the relative order period divided by
its gcd with \(m+1\), as in the label recurrence (1.13). A null derived
stratum contributes index \(1\) and leaves the label unchanged. The
proof of (1.15) uses the resulting ramification formula to select labels
for a prescribed ramification index.

The label map is noncanonical. Its construction in (1.4), (1.8) and
(1.14) uses prime elements, tame corestrictions and identifications of
residue fields with the finite fields in `Labels.lean`. The proposition
quantifies the map existentially.

Source. C. J. Bushnell and P. C. Kutzko, *Simple types in GL(N): computing
conjugacy classes*, Contemp. Math. 177 (1994), 107–135.
See printed p. 110 for the layer dimensions, (1.4)–(1.5), pp. 112–113,
(1.8), p. 114, (1.12)–(1.13), pp. 115–116, and (1.14)–(1.15),
pp. 116–117. PDF pages in the registered proceedings volume are the
printed pages plus 13. The source is
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
