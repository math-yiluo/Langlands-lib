# Jacquet modules of representations containing a non-maximal simple type of kind (a)

`PositiveDepthNonmaximalTypeJacquetStatement` takes a nonarchimedean local field \(F\),
an integer \(n>0\), an additive character \(\psi_F\) of \(F\), a subgroup \(J\) of
\(G=\mathrm{GL}_n(F)\) and a smooth complex representation \(\rho\) of \(J\). It assumes
that \((J,\rho)\) is a simple type exhibited by data of kind (a) of BK93 (5.5.10): a
simple stratum \(S=[\mathfrak A,m,0,\beta]\) in \(F^n\) with \(\mathfrak A\) principal, a
defining-sequence choice \(q\) and the period \(e=e(\mathfrak B_\beta\mid\mathfrak o_E)\)
of the centralizer order, \(E=F[\beta]\). This is `IsSimpleTypeData ψF S q e`, applied to
the pair transported to \(\mathrm{Aut}_F(F^n)\) by `glRepresentationToAut`; it includes
the condition that \(\psi_F\) has the conductor of BK93 §1.1.

If \(e\ge 2\), the statement asserts: every smooth complex representation \((\pi,V)\) of
\(G\) that contains \(\rho\) (`ContainsType π ρ`: there is a nonzero \(J\)-intertwining map
from \(\rho\) to the restriction of \(\pi\) to \(J\)) has a nonzero Jacquet module along a
proper block parabolic subgroup. Precisely, there are a block shape \(B\) whose standard
upper block parabolic subgroup \(P_B\) (`B.parabolic F`) is not all of \(G\), and an element
\(g\in G\), such that the coinvariants `Jacquet.Coinvariants π.representation
(B.conjugateUnipotent g)` of \(V\) under \(gU_Bg^{-1}\), the quotient of \(V\) by the span
of the vectors \(\pi(u)v-v\), are not a subsingleton. Here \(U_B\) is the unipotent
radical of \(P_B\). No irreducibility or admissibility of \(\pi\) is assumed. The field and
the carriers of \(\rho\) and \(\pi\) have independent universes.

## Source

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups* (1993), literature ID `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73` (PDF page = printed
page + 12):

- (7.3.2) and the first remark after it, printed p. 223. Let \(P=MU\) be a parabolic
  subgroup subordinate to the type and minimal for this property ((7.2.18), printed
  p. 221). The remark says that \(P\) is proper unless \(e(\mathfrak B\mid\mathfrak o_E)=1\).
  It also says that a representation containing \(\lambda\) contains \(\lambda_P\), so
  \(V^{\lambda_P}\ne0\), and then (7.3.2) gives \(V_U\ne0\).
- (7.3.6)(i), printed p. 225: the proof that \(V^{\lambda_P}\to V_U\) is injective uses
  only the smoothness of \(\pi\). This is why the statement asks for no admissibility.
- (7.2.17)(i), printed p. 220: \(\lambda=\mathrm{Ind}(\lambda_P)\) from
  \((J\cap P)H^1(\beta,\mathfrak A)\) to \(J\). By Frobenius reciprocity, every smooth
  representation that contains \(\lambda\) contains \(\lambda_P\), not only the
  irreducible ones of the remark.

The parabolic subgroup of §7.3 (printed p. 222) is the one given by (7.1.13)(i), printed
p. 213, for the \(E\)-decomposition \(V=V^{1}\oplus\dots\oplus V^{e}\) defined by (5.5.2):
\(P=G\cap\bigoplus_{i\le j}\mathrm{Hom}_F(V^{j},V^{i})\). In an \(F\)-basis that lists bases
of \(V^{1},\dots,V^{e}\) in this order, \(P\) is the standard upper block parabolic subgroup
with \(e\) blocks of size \(n/e\), and \(U\) is its unipotent radical. So \(U\) is a
conjugate \(gU_Bg^{-1}\), and \(P_B\ne G\) when \(e\ge2\). The Lean statement only asserts
that some proper block shape and some conjugating element exist. It does not record the
block sizes or which conjugate occurs. This is the form of the vanishing condition in
`GeneralLinear.IsSupercuspidal`.
