# Proof of the bounded-multiplicity Cartan series comparison

`Langlands.HarishChandraSchwartz.cartanLabelledSeries` proves
`CartanLabelledSeriesStatement`, the bounded-multiplicity comparison for
Renard's labelled Cartan series. [Statement](CartanLabelledSeriesStatement.md) ·
[Cartan cover correction](../../../notes/errata/renard-vii12-cartan-cover.md)

Suppose representatives \(x\in K_0zfK_0\) and \(y\in K_0z'f'K_0\)
have the same image under the left quotient map \(q\). Then \(y=cx\) with
\(c=yx^{-1}\in C\). Centrality gives \(y\in K_0(zc)fK_0\), and stability
under right multiplication by \(C\) gives \(zc\in P\). The ambient double
cosets containing \(y\) are equal, so the coarse Cartan hypothesis gives
\(f=f'\) and \(zc=z'\). Since \(q(zc)=q(cz)=q(z)\), injectivity on \(S\)
gives \(z=z'\). Thus distinct labels in \(F\times S\) give disjoint coarse
quotient cells.

Each refined cell \(q(Kk_i zf k_jK)\) lies in \(q(K_0zfK_0)\) by the
inclusions \(K\le K_0\) and \(k_i,k_j\in K_0\). The double coset is open
because \(K\) is open, and the open quotient map sends it to a Borel
set. For each fixed \((i,j)\), the refined cells form a countable disjoint
family indexed by \(F\times S\). Lean uses `lintegral_iUnion` to sum the
restricted integrals over this family and bounds the integral on its
union by the total integral. Summing over the \(r^2\) pairs \((i,j)\) gives
the upper bound on the labelled series.

Under the covering hypothesis, Lean applies `lintegral_iUnion_le` first
to the unions indexed by \((i,j)\), then to the cells indexed by
\((f,z)\) inside each union. This bounds the total integral by the labelled
series, including when cells for different compact label pairs overlap.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026. VII.1.2, from (VII.1.2.1) to (VII.1.2.2),
printed pp. 221–222 (PDF pp. 227–228). The coarse Cartan partition is
V.5.1(4), printed p. 122 (PDF p. 128). The chamber parameters and central
quotient are in V.3.23–24, printed p. 117 (PDF p. 123). Registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
