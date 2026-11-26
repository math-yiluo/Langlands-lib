# Split types of level \((x,0)\) for \(x>0\)

`IsPositiveZeroSplitType ψF x ρ` describes an irreducible pair arising
from a simple stratum \([\mathfrak A,n,0,\beta]\), where \(\mathfrak A\)
is hereditary and \(x=n/e(\mathfrak A)\). With the given additive
character of conductor \(\mathfrak p_F\) and a choice of defining
sequence, the predicate asks for
\(\theta\in\mathcal C(\mathfrak A,0,\beta)\),
a representation \(\eta\) of \(J^1(\beta,\mathfrak A)\) lying over
\(\theta\), and a \(\beta\)-extension \(\kappa\) of \(\eta\).
`IsPairIsomorphic` identifies the pair with
\((J(\beta,\mathfrak A),\kappa\otimes\xi)\).

The representation \(\xi\) of \(J(\beta,\mathfrak A)\) is smooth and
trivial on \(J^1(\beta,\mathfrak A)\). Put \(E=F[\beta]\) and
\(\mathfrak B_\beta=\mathfrak A\cap\operatorname{End}_E(V)\).
The restriction of \(\xi\) to \(U(\mathfrak B_\beta)\) is equivalent
to the inflation of the external tensor product of irreducible
cuspidal layer factors, with at least two inequivalent entries. It uses
`CuspidalLayerData` for the \(\mathfrak o_E\)-chain of \(\mathfrak B_\beta\).
The rank and isomorphism class of each factor are compared together.

`LatticeChain.relativeUnitFiltrationEquiv` identifies the units of the
centralizer chain with the subgroup commuting with the generator in
the base chain's unit filtration. The map restricts scalars, and its
surjectivity follows by lifting both a commuting unit and its inverse
to \(E\)-linear endomorphisms. At depth zero, this identifies the domain
of the inflation with the published `relativeUnitFiltration` subgroup,
whose inclusion in \(J(\beta,\mathfrak A)\) defines the restriction of
\(\xi\). The defining conditions on \(\xi\) refer to this restriction
and to triviality on \(J^1\), the two pieces of the finite-quotient
description in (8.1.4)(ii)(b).

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (8.1.4), printed p. 267, and §1.2,
printed pp. 24–26, for the centralizer order and its filtration.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
