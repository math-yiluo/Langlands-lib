# Initial convergence of complex matrix zeta integrals

`complexMatrixZeta` uses the determinant-weighted Haar measure and
the shift \((n-1)/2\) in the matrix integral of Jacquet,
*Archimedean Rankin–Selberg integrals*, §4.7. A measurable coefficient
with a polynomial height bound gives absolute convergence in a right
half-plane, as in the estimate used in his Lemma 3.3. The integral is
holomorphic on the open half-plane specified by the bound.

Multiplying the height by \(\lvert\det X\rvert_{\mathbb C}\) replaces
the inverse-matrix entries by adjugate entries. Leibniz estimates bound
the determinant and these entries by polynomials in the matrix norm.
After converting Haar measure to additive matrix measure, the remaining
determinant exponent is nonnegative for sufficiently large real part.
It too is bounded by a polynomial in the matrix norm, for each exponent.
The Schwartz decay supplies an integrable majorant. Holomorphy follows
from the Library's differentiation theorem for exponential integrals.
