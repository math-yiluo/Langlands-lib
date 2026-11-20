# Nonvanishing of the complex strict swap product with an ordered source

The product of diagonal entry norms squared on the unitary group takes
values in \([0,1]\). It can attain one only when every row is supported on its
diagonal entry. This follows from the row norm identity for unitary matrices.
Increasing the nonnegative exponents in the Library's phase monomial at every
position by \(N\) multiplies the corresponding phase vector by the \(N\)th
power of this function evaluated on the compact factor. The starting vector
is one at the identity.

`StrictSwapChain.intertwiner_ne_zero` evaluates the product integral at the
inverse of the chain permutation matrix. The resulting chart takes values
in lower unitriangular matrices and sends zero to the identity. The proof
uses an open neighborhood of the identity on which the real part of the
initial phase vector exceeds \(1/2\). Compact coordinate recovery gives a
uniform upper bound \(c<1\) on the diagonal product outside this neighborhood.
On a small ball in the parameter space the real part exceeds \(1/2\) and the
diagonal product is bounded below by some \(\delta>c\).

After the \(N\)th power, the positive contribution from this ball is bounded
below by its volume times \(\delta^N/2\). The negative contribution is bounded
in absolute value by \(c^N\) times the integral of the absolute value of the
initial phase vector. That integral is finite by the chain integrability
theorem. The ratio \((c/\delta)^N\) tends to zero, so the real part of the
integral is positive for some \(N\). The corresponding compact-finite vector
therefore has nonzero image under the composite.

The compact-model localization is an internal construction for the
intertwining integral, following the use of local test sections in Wallach,
*Real Reductive Groups I* (1988), Lemma 5.3.1, printed pp. 144–145 (PDF pp.
164–165 of `wallach-1988-real-reductive-groups-i`). Its application is the
archimedean constituent step in Getz and Hahn, *An Introduction to Automorphic
Representations* (2024), Theorem 10.6.4, printed p. 286 (PDF p. 298 of
`getz-hahn-2024-automorphic-representations`).
