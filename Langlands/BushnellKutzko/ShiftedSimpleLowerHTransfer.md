# Isotypic transfer from the shifted first H group

`SplitBlocks.ShiftedSimpleLowerHTransferStatement` concerns a simple
stratum \([\mathfrak A,n,0,\beta]\) with a defining sequence over a
nonarchimedean local field. For a BK additive character it takes a simple
character \(\theta\) of \(H^1\) at index zero, with \(1<n\) and \(1\)
below critical depth. The complementary orthogonal idempotents \(e_1,e_2\)
lie in the integral centralizer. The unit \(z=\zeta+e_2\) has inverse
\(\zeta'+e_2\), with \(\zeta\) and \(\zeta'\) in the \((1,1)\) corners
of the centralizer lattices of depths \(1\) and \(-1\) and
\(\zeta\zeta'=e_1\). Let \(c\in\mathfrak P^{-1}\) commute with both
idempotents. On the subgroup \(K\) of \(H^1\) with lower corner of depth
at least two, the character \(\vartheta\) is the restriction of \(\theta\)
twisted by \(\psi_c\).

Let \(M\) be a subgroup of the upper block unipotent group in a complex
representation. A vector outside the \(M\) Jacquet relations on which
\(z^{-1} h z\) acts by \(\theta(h)\psi_c(z^{-1} h z)\) for all
\(h\in H^1\) gives a \(\vartheta\)-isotypic vector for \(K\) outside those
relations.

`SplitBlocks.exists_isotypic_of_shiftedSimpleLowerH` implements a
depth-one transfer for the unequal-level argument of Bushnell–Kutzko
(1993), §8.2. It uses the lower extension of the simple character
in (8.2.18)–(8.2.20), the \(H\)-square estimate of (8.2.13) for upper-unit
normalization, and the trace annihilator of the first \(J\) lattice from
(3.1.21) at depth one. After conjugating the starting vector and the
relations by \(z\), the depth-one averaging lemma
makes the vector isotypic for \(H^1\) enlarged by the lower part of
\(J^1\). Conjugating back gives the desired character on the subgroup of
\(K\) where the shifted lower entry belongs to the first \(J\) lattice.
Indeed, for \(k=1+x\) in this subgroup, factor \(k=(kd^{-1})d\) with
\(d=1+e_2xe_1\). The conjugate of \(d\) belongs to the lower part of
\(J^1\). The shifted lower entry of \(kd^{-1}\) belongs to the second
\(H\) lattice by \(\mathfrak j^1\mathfrak j^1\subseteq\mathfrak h^2\)
from (3.1.13)(ii). Its conjugate belongs to \(H^1\) and has the same
simple-character value by centralizer intertwining (3.3.2), evaluated
by `simpleCharacter_conj_of_commute`.

The shifted upper units from the cutoff \(H\) lattice normalize \(H^1\)
and become elements of \(H^1\) after conjugating by \(z\). Their action
fixes the lower extension on the kernel of the reference trace pairing
and fixes the diagonal trace twist there. The finite-character transfer
then gives the asserted vector on \(K\).

Source. C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N)
via compact open subgroups* (1993), (3.1.13)(ii), (3.1.21), (3.3.2),
(8.2.13), and (8.2.18)–(8.2.20), printed pp. 94, 97, 105, 280,
and 284–285 (PDF pp. 106, 109, 117, 292, and 296–297). Literature ID
`bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
