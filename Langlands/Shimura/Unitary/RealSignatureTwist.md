# Prescribing all real signatures by a symmetric unit

Let \(E\) be a totally real number field, \(K/E\) a CM quadratic
extension, and \(A\) a degree-\(n\) central simple \(K\)-algebra with
\(n>1\). The given second-kind involution on \(A\) induces CM
conjugation on \(K\). At each real embedding \(\tau\) of \(E\), prescribe
a positive dimension \(0\le r(\tau)\le n\). The corresponding matrix
is \(J=\operatorname{diag}(1_{r(\tau)},-1_{n-r(\tau)})\).

The real scalar extension has complex matrix coordinates and a
Hermitian Gram matrix \(H\) for the given involution. In those
coordinates \(H^{-1}J\) is fixed by the adjoint for \(H\). Twisting by
\(H^{-1}J\) gives Gram matrix \(J\) at that place.

The finite-dimensional real matrix coordinates are continuous in the
scalar extension of a basis of the original algebra. Weak approximation
provides one global element whose coordinates, after averaging with its
image under the involution, put every twisted Gram matrix in the open
neighborhood of its prescribed signature. The congruences make the
symmetric element invertible at each real embedding. Faithful scalar
extension and the finite-dimensional left multiplication map reflect
invertibility back to the original algebra.

`realSignatureTwist` uses this symmetric unit to twist the original
involution on \(A\). At each real embedding the Gram matrix is
congruent to the prescribed one. The change of basis gives the
`HasSignature` equivalence from \(\mathbb R\otimes_{E,\tau}A\) to
\(M_n(\mathbb C)\) with the adjoint for \(J\).
