# Maximal simple type pairs in matrix coordinates

Let \(F\) be a nonarchimedean local field and \(N\ge 1\). `GLRepresentationPair`
is the type of pairs \((J,\lambda)\) of a subgroup of `GeneralLinear N F` and
a smooth complex representation of \(J\). The universe of representation
carriers is a parameter independent of the field universe. The sets
below apply `glRepresentationToAut` from `GLSimpleTypes` to use the
lattice-chain definitions on \(F^N\).

For \(t,m\ge 1\), `glMaximalSimpleTypesAt N F t m` is the set of pairs
exhibited by kind (a) data at a principal order \(\mathfrak A\) of period
\(t\), with simple stratum \([\mathfrak A,m,0,\beta]\) and centralizer order
\(\mathfrak B_\beta\) of period one over \(\mathfrak o_{F[\beta]}\). The
additive character is a witness of membership with the conductor required
by `IsSimpleTypeData`. `glMaximalLevelZeroSimpleTypes N F` consists of
the pairs exhibited by kind (b) data on a principal order of period one.
Both period-one conditions give `IsGLMaximalSimpleType` from the
corresponding data. Membership is existential in the exhibiting data and
a pair can meet more than one specification.

The conjugacy relation on these pairs is `AreConjugatePairs` specialized
to the matrix group and the two underlying algebraic representations.
Thus for some \(g\in \mathrm{GL}_N(F)\) the second subgroup is
\(gJ_1g^{-1}\) and pullback of its representation along \(j\mapsto gjg^{-1}\)
is equivalent to the first.

In BK94, \(T_m(\mathfrak A)\) is the set of \(U(\mathfrak A)\)-conjugacy
classes of simple types over a single principal order \(\mathfrak A\).
The Lean sets consist of maximal simple type pairs over all principal
orders of the specified period in \(\mathrm{GL}_N(F)\), as used for the
global conjugacy classes in (3.8). At level zero the specified period is
one.

## Sources

- Bushnell–Kutzko, *Simple types in GL(N): computing conjugacy classes*
  (1994), §3, \(T_m(\mathfrak A)\), \(T_0(\mathfrak A)\), (3.7) and (3.8),
  printed pp. 125–126 (volume PDF pp. 138–139).
  Literature ID `bushnell-kutzko-1994-simple-types-conjugacy-classes`,
  SHA-256 `fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
- Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
  (1993), maximality before (6.2.3), printed p. 204 (PDF p. 216).
  Literature ID `bushnell-kutzko-1993-admissible-dual-gln`,
  SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
