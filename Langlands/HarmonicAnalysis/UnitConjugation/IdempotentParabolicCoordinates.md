# Coordinates for an idempotent parabolic

For an idempotent \(e\) of a finite-dimensional topological \(F\)-algebra
\(A\), let \(P\) be the upper triangular subgroup of \(A^\times\),
\(M\) the unit group of the centralizer algebra of \(e\) inside \(A^\times\),
and \(U=1+eA(1-e)\). The topology on each subgroup is induced by
\(A^\times\). The declaration `leviUnitsEquiv` identifies the unit group of
the centralizer algebra with \(M\) as a topological group.

`parabolicUnitsHomeomorph` identifies \(M\times U\) with \(P\) by
\((m,u)\mapsto mu\). To construct the inverse, regard \(p\in P\) as a unit
of the upper triangular subalgebra. Its value and its inverse have zero
opposite corner. Applying the diagonal-block algebra homomorphism to this
unit gives \(m\in M\). For every factorization \(p=lu\) with \(l\in M\)
and \(u\in U\), the diagonal of \(lu\) equals \(l\). Thus \(m=l\) and
\(m^{-1}p=u\). The diagonal projections of the value and inverse coordinates
are continuous. Multiplication and inversion give continuity of
\(p\mapsto(m,m^{-1}p)\).

These are the Levi and unipotent coordinates used in the Haar factorization
in Harish-Chandra's *Admissible invariant distributions on reductive
\(p\)-adic groups*, §1.2, printed p. 7. As a homeomorphism the coordinate map
identifies the compact intersection \(P\cap K\) with its compact preimage
in \(M\times U\) for a compact subgroup \(K\) of a Hausdorff ambient unit
group. Here \(P\) is closed by the opposite-corner equation.
