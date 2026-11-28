# Shifted H groups and their overlap

`SplitBlocks.shift_conj_mem_simpleHGroup_iff` describes the overlap of
\(H^m\) with its conjugate under \(z=\zeta+e_2\) for a simple stratum of
index zero and a defining sequence. The inverse is \(\zeta'+e_2\), with
\(\zeta\) and \(\zeta'\) in the centralizer lattices of depths \(1\) and
\(-1\), \(e_2\) in the integral centralizer, and \(e_1\zeta'=\zeta'\).
For \(k\in H^m\) with \(m\geq 1\), membership of \(zkz^{-1}\) in \(H^m\)
is equivalent to membership of \(e_2(k-1)e_1\zeta'\) in the \(H\) lattice
at depth \(m\). The proof expands the conjugation and uses stability
under the integral centralizer and the commuting actions of the
fractional centralizer lattices on the other three terms.

With \(e_2e_1=0\), \(e_2^2=e_2\), and \(\zeta\zeta'=e_1\),
`SplitBlocks.shift_conj_blockUnit` sends \(1+e_1\zeta'ye_2\) to
\(1+e_1ye_2\) by the same conjugation. These are the block calculations
for the shift of Bushnell–Kutzko (1993), (8.2.9) and (8.2.26).

`SplitBlocks.simpleCharacter_conj_of_commute` evaluates a simple character
on elements of its domain that are conjugate by a unit commuting with
\(\beta\). It uses a BK additive character and an index \(i\) for which
\(i+1\) is below both the stratum depth and the critical depth. The unit lies in the
centralizer term of the intertwining set of (3.3.2), printed p. 105.
The Lean proof applies `simpleCharacterCovariance`, which extends the
covariance calculation of (3.3.9), printed p. 108. Commutation with
\(\beta\) makes the trace twist zero.
