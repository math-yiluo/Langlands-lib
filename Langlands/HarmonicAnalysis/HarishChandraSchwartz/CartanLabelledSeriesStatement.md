# The labelled Cartan series with bounded multiplicity

Let \(C\) be a central subgroup of a topological group \(G\), and write
\(q:G\to C\backslash G\) for the quotient map. Let \(K\) be an open
subgroup of \(G\) contained in \(K_0\). Suppose \(P\subseteq G\) is
stable under right multiplication by \(C\). The parameter set \(S\)
is contained in \(P\), and \(q\) is injective on \(S\).
The parameter sets \(F\) and \(S\) are countable. Assume that equality
of the ambient double cosets \(K_0zfK_0\) and \(K_0z'f'K_0\), for
\(f,f'\in F\) and \(z,z'\in P\), implies \(f=f'\) and \(z=z'\).

Given \(r\) points \(k_i\in K_0\), the proposition asserts disjointness
of the sets \(q(K_0zfK_0)\) for distinct \((f,z)\in F\times S\).
For a Borel measure \(\mu\) on the quotient and a nonnegative extended
real density \(a\), write \(D_{i,j,f,z}=q(Kk_i zf k_jK)\). Then
\[
  \sum_{i,j,f,z}\int_{D_{i,j,f,z}} a\,d\mu
    \le r^2\int_{C\backslash G}a\,d\mu.
\]
If the labelled cells cover the quotient, the integral is bounded above
by the same sum. In particular the integral and series are finite
together. A density that is constant on a cell gives its value times
the cell mass in the corresponding summand.

In Renard's application, \(P=C_{\varnothing}^+\), \(F=F_{\varnothing}\),
and \(C=C_{A_G}\). The ambient disjointness is the coarser Cartan
partition of V.5.1(4). The uniformizer subgroup \(C\) acts in the
central directions of \(P\). The lifting set \(S\) has one representative
in each \(C\)-class of \(P\), and the elements \(f\) commute with the
uniformizer torus, so the two product orders give the same cells.
The proof of VII.1.2 expects equality for the refined labelled sum.
The bound allows repetitions within the finite pair of compact labels.
[Cartan cover correction](../../../notes/errata/renard-vii12-cartan-cover.md)

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026. VII.1.2, Cartan expansion from (VII.1.2.1) to
(VII.1.2.2), printed pp. 221–222 (PDF pp. 227–228), V.5.1(4), printed
p. 122 (PDF p. 128), and V.3.23–24, printed p. 117 (PDF p. 123).
Registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
