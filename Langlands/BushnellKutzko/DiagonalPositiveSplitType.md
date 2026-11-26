# Split types of level \((x,x)\) for \(x>0\)

`IsDiagonalPositiveSplitType ψF x ρ` describes a pair \((K,\vartheta)\) in
\(\operatorname{Aut}_F(V)\). Its witness `S` is a split fundamental
stratum \([\mathfrak A,n,n-1,b]\) with \(n>0\). The lattice chain of
\(\mathfrak A\) supplies its period \(e\), and the predicate requires
\(\gcd(n,e)=1\) and \(x=n/e\) in \(\mathbb Q\). `IsPairIsomorphic`
identifies \(K\) with \(U^n(\mathfrak A)\) and \(\vartheta\) with the
one-dimensional representation on \(\mathbb C\) attached to \(\psi_b\).

The conductor condition is `IsBKAdditiveCharacter ψF`.
`filtrationTraceCharacter` applies `additiveDuality` with \(r=m-1\)
to obtain the character on \(U^m(\mathfrak A)\) for
\(b\in\mathfrak P^{-m}\), \(m>0\). Its evaluation is
\(\psi_b(g)=\psi_F(\operatorname{tr}_A(b(g-1)))\), and its restriction to
\(U^{m+1}(\mathfrak A)\) is trivial. For the split stratum, the valuation
bound supplies the required filtration membership with \(m=n\).

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (8.1.1), printed p. 266,
and (1.1.6), printed p. 22, for the character construction.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
