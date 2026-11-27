# Extracting an extension in the induced degree

This abstracts the degree comparison in Bushnell–Kutzko (1993),
(5.1.14)–(5.1.17), printed pp. 163–164 (PDF pp. 175–176), and (5.2.5),
printed pp. 169–170 (PDF pp. 181–182). The retained source
`bushnell-kutzko-1993-admissible-dual-gln` has SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

Let \(H\le A\le G\) be groups with \([G:A]\) finite. Let \(\rho\) be
a finite-dimensional complex representation of \(H\) on \(V\), and let
\(\pi\) be a finite-dimensional complex representation of \(G\) on
\(W\). Suppose \(\pi|_H\) contains a split copy of \(\rho\): an
\(H\)-equivariant linear inclusion \(i\colon V\to W\) and an
\(H\)-equivariant linear retraction \(p\colon W\to V\) with
\(p\circ i=\mathrm{id}_V\). Assume that every element of \(G\) which
intertwines \(\rho\) with itself lies in \(A\), and that
\(\dim_{\mathbb C} W=[G:A]\dim_{\mathbb C} V\). Then \(\rho\) extends
on \(V\) to a representation \(\kappa\) of \(A\) whose coinduction to
\(G\) is equivalent to \(\pi\). Every \(H\)-equivariant linear map
\(j\colon V\to W\) satisfies \(j=i\circ(p\circ j)\), so it factors
through \(i\). The two representation spaces and the group have
independent universes.

The intermediate subgroup in (5.1.14) contains the Heisenberg
subgroup and its self-intertwining inside the larger unit group.
The comparison of induced degrees (5.1.17) gives the dimension
hypothesis. At finite index, coinduction is equivalent to induction.
