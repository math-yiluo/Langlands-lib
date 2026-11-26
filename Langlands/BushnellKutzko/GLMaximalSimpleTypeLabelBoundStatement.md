# Labels bounding the maximal simple type classes

Let \(F\) be a nonarchimedean local field with residue field \(k_F\) of
cardinality \(q_F\), and let \(N\ge 1\). The matrix group is
`GeneralLinear N F`. The representation carriers range over a universe
independent of that of \(F\).

For every positive divisor \(t\) of \(N\) and every \(m\ge 1\),
`GLMaximalSimpleTypeLabelBoundStatement` asserts that there is a map
\[
    L:\mathcal T_{t,m}(N,F)\longrightarrow\widetilde P_m(t,N/t;q_F).
\]
Here \(\mathcal T_{t,m}\) is `glMaximalSimpleTypesAt N F t m`. The target is
`extendedLabelSet m t (N / t) qF`, with top level \(m\) and bottom level zero.
Each value \(L(x)=(p,\phi)\) has `Label.e p = 1`. Two pairs with the same
label are \(\mathrm{GL}_N(F)\)-conjugate by `AreConjugatePairs`.
At level zero there is a map
\[
    L_0:\mathcal T_0(N,F)\longrightarrow\widetilde P_0(1,N;q_F)
\]
with the same implication for equal labels. Here \(\mathcal T_0\) is
`glMaximalLevelZeroSimpleTypes N F` and the target is
`degenerateLabelSet N qF`.

BK94 (3.7)–(3.8) give bijections for all simple types. This statement
uses the direction in which equality of labels forces conjugacy, for
maximal simple types. In positive depth, centralizer order period one
in BK93's definition of maximality is the case \(e(p)=1\) of the labels.
At level zero the maximal case has original order period one.

The number of conjugacy classes met by either set is bounded by the
number of possible labels, since the pairs with each given label belong
to one class. Combining the fiber implication with
`Langlands.Henniart.BushnellKutzkoLabelCountStatement` for the labels in
`Labels`, using \(n=N\) and \(f=N/t\) at positive depth, gives at most
`polarPartCount qF N (N / t) ((N / t) * m)` classes there and at most
`polarPartCount qF N N 0` classes at level zero.

## Sources

- Bushnell–Kutzko, *Simple types in GL(N): computing conjugacy classes*
  (1994), the extended labels on printed p. 125, (3.7)–(3.8) and the
  level-zero labels on p. 126 (volume PDF pp. 138–139).
  Literature ID `bushnell-kutzko-1994-simple-types-conjugacy-classes`,
  SHA-256 `fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
- Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
  (1993), maximality before (6.2.3), printed p. 204 (PDF p. 216).
  Literature ID `bushnell-kutzko-1993-admissible-dual-gln`,
  SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
