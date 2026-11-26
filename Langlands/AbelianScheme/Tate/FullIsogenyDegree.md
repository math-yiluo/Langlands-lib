# The full integral Tate cokernel of an isogeny

Let \(f:A\to B\) be an isogeny of abelian schemes over a scheme \(S\).
For a point \(s:\operatorname{Spec}\Omega\to S\) with \(\Omega\) algebraically
closed of characteristic zero, `fullIsogenyCokernelEquiv` identifies the
cokernel of \(T(f)\) on the full integral Tate groups at \(s\) with the
additive group of \(\Omega\)-valued kernel points of \(f\) over \(s\).
Here \(T\) is the inverse limit over all positive torsion orders.

Write \(\varphi:A_s(\Omega)\to B_s(\Omega)\) for the map on points.
The isogeny gives a surjective homomorphism with finite kernel, so
`GroupScheme.exists_pow_quasiInverse` supplies a homomorphism
\(\psi:B_s(\Omega)\to A_s(\Omega)\) with both composites multiplication
by a positive integer \(N\). The map from \(T(B_s)\) to \(\ker\varphi\)
sends a family \(b\) to \(\psi(b_N)\). It is surjective because
\(A_s(\Omega)\) is divisible by \(N\) and the \(N\)-th projection of
\(T(B_s)\) is surjective. If \(\psi(b_N)=0\), the points
\(\psi(b_{Ni})\), indexed by positive integers \(i\), form a full Tate
family of \(A_s\). Its image under \(T(f)\) is \(b\). Conversely the
image of \(T(f)\) is killed by the map to \(\ker\varphi\), since its
composite at level \(N\) is multiplication by \(N\) on \(N\)-torsion.
The first isomorphism theorem then gives the additive equivalence.

`finrank_eq_card_fullIsogenyCokernel` combines this description with
`isogenyFinrankKernelCard` for an isogeny over an algebraically closed
field of characteristic zero. Its rank at any point of the target is
the cardinality of the integral Tate cokernel.
`finrank_eq_card_fullIsogenyCokernel_at` gives the relative version at
each point of the target's geometric fibre over \(s\), by invariance of
native rank under pullback and the base-change identification of
geometric kernel points. These formulas derive from the Library's
point divisibility, isogeny kernel and integral Tate constructions.
