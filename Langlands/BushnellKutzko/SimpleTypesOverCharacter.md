# Simple types over a fixed simple character

Let \(F\) be a nonarchimedean local field, \(V\) a nonzero finite-dimensional
\(F\)-vector space, and \(\psi_F\) an additive character of conductor
\(\mathfrak p_F\) in the convention of `IsBKAdditiveCharacter`. Let
\([\mathfrak A,n,0,\beta]\) be a simple stratum on a principal order and let
\(\theta\in C(\mathfrak A,0,\beta)\). `IsSimpleTypeOver ψF S q θ ρ` says that
the representation \(\rho\) of \(J(\beta,\mathfrak A)\) is a simple type over
\((\mathfrak A,\beta,\theta)\), with the groups realized using the defining
sequence `q` of `S`.

`IsSimpleTypeDataOver` specifies which character witnesses the kind (a) data
and records the centralizer order period \(e\). The Heisenberg representation
over \(\theta\), its \(\beta\)-extension, the cuspidal representation of
\(\mathrm{GL}_f(k_E)\), and the layer bases remain existential. The definition
uses the same `IsHeisenbergRepresentation`, `IsBetaExtension`,
`IsLayerReduction`, tensor power, inflation conditions, and `IsPairIsomorphic`
as `IsSimpleTypeData`. The equivalence
`isSimpleTypeData_iff_exists_isSimpleTypeDataOver` recovers `IsSimpleTypeData`
by quantifying over the character. `IsSimpleTypeOver` specializes the
subgroup to \(J(\beta,\mathfrak A)\) and quantifies over \(e\).

BK94 calls this a simple type over \(\theta\). The Lean predicate also records
\(\mathfrak A\) and \(\beta\) through the stratum. Taking \(u=1\) in BK94
(3.4) shows that only \(\theta\), with its domain, matters at the fixed order
and stratum level. Equal subgroup–character pairs give equal \(J\)-groups
and identify the simple types over the two presentations.

## Source

Bushnell–Kutzko, *Simple types in GL(N): computing conjugacy classes* (1994),
§3, the construction of \(\lambda=\kappa\otimes\sigma\) and (3.4), printed
p. 124 (volume PDF p. 137).
Literature ID `bushnell-kutzko-1994-simple-types-conjugacy-classes`,
SHA-256 `fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
