# Simple-type exhaustion for supercuspidal representations

`SupercuspidalSimpleTypeExistenceStatement` is the existence assertion
of (8.4.1). It applies to every nonarchimedean local field \(F\),
every \(n>0\), and every additive character \(\psi_F\) trivial on
\(\mathfrak p_F\) and nontrivial on \(\mathfrak o_F\).
If a smooth complex representation \(\pi\) of \(\mathrm{GL}_n(F)\)
satisfies `GeneralLinear.supercuspidalProperty`, then it contains
an `IsGLSimpleType` pair for that \(\psi_F\). The field, the carrier
of \(\pi\), and the type carrier have independent universes.

`GeneralLinear.supercuspidalProperty` supplies irreducibility,
admissibility, and vanishing for every proper parabolic Jacquet
module. In the source argument this vanishing excludes split
types by (8.2.5) and (8.3.3), so (8.1.5) gives the existence of
a simple type. `ContainsType` expresses the conclusion as a
nonzero intertwining map into the restriction of \(\pi\).

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (8.4.1), first assertion, printed p. 297.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
