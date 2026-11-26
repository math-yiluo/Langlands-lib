# Split types of level \((x,y)\) for \(x>y>0\)

`IsUnequalPositiveSplitType ψF x y ρ` requires `IsBKAdditiveCharacter ψF`.
The additive character is trivial on \(\mathfrak p_F\) and nontrivial
on \(\mathfrak o_F\). The same character defines the simple character
set and the trace character \(\psi_c\).

The predicate uses a simple stratum
\(S=[\mathfrak A,n,m,\beta]\) with \(m=j+1\) for a natural number \(j\).
The levels are \(x=n/e(\mathfrak A)\) and \(y=m/e(\mathfrak A)\).
Here the stratum inequality \(m<n\) and the positive period give \(x>y>0\).
The simple stratum supplies a field structure on \(E=F[\beta]\), and
`LatticeChain.subfieldChain` constructs the \(\mathfrak o_E\)-chain of
\(\mathfrak B=\mathfrak A\cap\operatorname{End}_E(V)\). Its period gives
the coprimality condition \(\gcd(m,e(\mathfrak B\mid\mathfrak o_E))=1\).

The witnesses are a simple character
\(\theta\in\mathcal C(\mathfrak A,m-1,\beta)\) for the chosen defining
sequence, an element \(c\in\mathfrak P^{-m}\), and a tame corestriction
\(s\) relative to \(E/F\). `LatticeChain.corestrictedStratum`
constructs \([\mathfrak B,m,m-1,s(c)]\) using the filtration-image
formula for \(s\). The predicate requires `Stratum.IsSplit` of this
derived stratum. `IsPairIsomorphic` identifies the pair with
\((H^m(\beta,\mathfrak A),\theta\psi_c)\). The multiplicative character
\(\psi_c\) comes from `filtrationTraceCharacter` and is restricted
along \(H^m(\beta,\mathfrak A)\le U^m(\mathfrak A)\).

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (8.1.3), printed p. 267, with the
conductor convention in §8.1, printed p. 266, the filtration image
in (1.3.4)(ii), printed p. 29, and the derived stratum in §2.2,
printed p. 51.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
