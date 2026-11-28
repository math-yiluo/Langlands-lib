# Isotypic transfer from the shifted overlap at depth at least two

`SplitBlocks.ShiftedLowerCornerTransferStatement` concerns a simple
stratum \([\mathfrak A,n,0,\beta]\) over a nonarchimedean local field
with a defining sequence and a BK additive character. It uses a simple
character \(\theta\) of \(H^m\) at index \(m-1\) with \(2\leq m<n\)
and \(m\) below critical depth. The complementary orthogonal idempotents
\(e_1,e_2\) are in the integral centralizer. The shift
\(z=\zeta+e_2\) has inverse \(\zeta'+e_2\), with \(\zeta\) and
\(\zeta'\) in the centralizer lattices of depths \(1\) and \(-1\),
\(\zeta\zeta'=e_1\), and \(e_1\zeta'=\zeta'\). On the subgroup \(K\)
of \(H^m\) whose lower corner has depth at least \(m+1\), the character
\(\vartheta\) is the restriction of \(\theta\) times the trace twist
by \(c\in\mathfrak P^{-m}\) commuting with both idempotents.

For a complex representation and a subgroup \(M\) of the upper block
unipotent group, a vector outside the \(M\) Jacquet relations that
transforms through \(\vartheta\) on the subgroup of \(K\) with
\(zkz^{-1}\in H^m\) gives a \(\vartheta\)-isotypic vector outside
the same relations.

`SplitBlocks.exists_isotypic_of_shiftedHOverlap` uses the shift of
Bushnell–Kutzko (1993), (8.2.9), printed p. 278, and adapts the
character comparison of (8.2.26) to \(K\). The source comparison
upgrades isotypy on the product of \(U^m(\mathfrak B)\) and the full
shifted overlap to isotypy on \(H^m\), printed pp. 288–289.

The proof uses the \(H\)-lattice trace dual of (3.1.19), printed
pp. 96–97, with book index \(m-1\). Its adjoint image of the cutoff
\(J\) lattice gives the reference pairing. The mixed product estimate
extending (8.2.28) shows that the shifted upper units normalize \(H^m\)
by the square-zero criterion. After conjugation by \(z\) these units
belong to \(J^1\) and normalize \(\theta\) by (3.3.1), printed p. 104.
The centralizer intertwining in (3.3.2), printed p. 105, gives equality
of \(\theta\) with its conjugate under \(z\) on the overlap. Lean computes
that equality using `simpleCharacter_conj_of_commute`. Integral upper
conjugation fixes the diagonal trace twist, so
`SplitBlocks.exists_isotypic_of_lowerCornerKernel` applies.
