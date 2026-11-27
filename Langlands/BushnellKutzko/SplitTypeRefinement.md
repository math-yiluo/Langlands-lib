# Jacquet nonvanishing by refinement along a filtration

This module contains two abstract steps used for the nonvanishing of
Jacquet modules of split types, Bushnell–Kutzko (8.2.5)(iv). It works
with an arbitrary complex representation \(\rho\) of a group \(G\) and
the coinvariant relations `Jacquet.relations ρ N`, the span of the
vectors \(\rho(n)v-v\) for \(n\in N\). It uses no topology.

## Relations

- `relations_mono`: the relations grow with the subgroup.
- `apply_mem_relations`: if \(gNg^{-1}\subseteq N'\), then \(\rho(g)\)
  carries the relations of \(N\) into those of \(N'\).
- `exists_mem_relations_of_exhaustive`: if an antitone family
  \((M_j)_{j\in\mathbb Z}\) of subgroups covers \(U\), every relation of
  \(U\) is a relation of some \(M_j\). A relation is a finite
  combination of generators, and each generator involves one element
  of \(U\).
- `not_subsingleton_of_not_le_relations`: if some vector is not a
  relation of \(U\), the coinvariants `Jacquet.Coinvariants ρ U` are
  nonzero.

## Descent along a filtration

`not_le_relations_of_refinement` takes a finite-dimensional subspace
\(P\) and such a family \((M_j)\). Suppose \(P\not\subseteq\mathrm{rel}(M_{j_0})\)
for one \(j_0\), and suppose that \(P\not\subseteq\mathrm{rel}(M_j)\)
implies \(P\not\subseteq\mathrm{rel}(M_{j-1})\) for every \(j\). Then
\(P\not\subseteq\mathrm{rel}(U)\). Induction gives non-containment for
every \(M_{j_0-k}\), \(k\ge 0\). If \(P\subseteq\mathrm{rel}(U)\), each
vector of a basis of \(P\) is a relation of some \(M_j\). The family is
antitone, so all of them are relations of the smallest of these
finitely many \(M_j\). That contradicts the first step. This is the
choice of a maximal \(j\) in BK93, printed p. 281: by admissibility the
isotypic subspace there is finite-dimensional.

## Transfer to a larger group

For subgroups \(K\) and \(\mathcal K\) of \(G\) with \(K/(K\cap\mathcal K)\)
finite, and a character \(\chi\) of \(K\), `twistedCosetSum` is
\(\sum_{c\in K/(K\cap\mathcal K)}\chi(c)^{-1}\rho(c)v\) over chosen
representatives. `twistedCosetSum_isotypic` shows that it is
\(\chi\)-isotypic for \(K\) when \(K\cap\mathcal K\) acts on \(v\) through
\(\chi\).

`exists_isotypic_not_mem_relations` is the transfer step. The
hypotheses are:

- \(K\cap\mathcal K\) acts on \(v\) through a character \(\vartheta\) of
  \(K\), and \(v\notin\mathrm{rel}(M)\);
- a nonempty finite family of characters \(\chi_z\) of \(K\) agrees with
  \(\vartheta\) on \(K\cap\mathcal K\);
- elements \(g_z\) carry \(\chi_z\)-isotypic vectors to
  \(\vartheta\)-isotypic ones and satisfy \(g_z^{-1}Mg_z\subseteq M\);
- the orthogonality relation \(\sum_z\chi_z(k)^{-1}\) equals
  \(|Z|\,\vartheta(k)^{-1}\) for \(k\in K\cap\mathcal K\) and \(0\) for
  the other \(k\in K\).

Then some \(\vartheta\)-isotypic vector for \(K\) is not in
\(\mathrm{rel}(M)\). By orthogonality the twisted coset sums for the
\(\chi_z\) add up to \(|Z|\,v\), so one of them is not a relation of
\(M\). Translating it by \(g_z\) gives the required vector. The
relations of \(M\) are stable under \(g_z^{-1}\), which is what this
translation needs.

This is a form of BK93 (8.2.14), printed p. 281. That lemma uses a
decomposition of the span of the \(\mathcal H\)-translates of \(v\)
into isotypic components, and assumes that the extensions of the
character are all conjugate under elements normalizing the subgroups
involved. The version here replaces the conjugacy assumption by the
orthogonality relation for the given family.

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (8.2.14), printed pp. 281–282, and the
argument of printed p. 281.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
