# Actual affine-line maps in polynomial kernels

Worker 864. Internal adapter for the central additive-subgroup criterion, derived
from the polynomial curve and actual geometry constructions associated with CGP,
*Pseudo-reductive groups*, second edition, Lemmas B.1.7–B.1.9, printed pp.563–565
(one-based PDF pp.589–591).

`affineLinePolynomialCoordinates` chooses coordinate polynomials for every actual
affine-line map to a standard vector group. Its evaluation theorem recovers the
original global-function coordinates.

For any field and finite row of additive polynomials, an actual affine-line map
into the actual categorical kernel yields coordinate polynomials whose composition
sum is exactly zero. This uses the bijection from the polynomial ring to global
functions on the affine line and the actual kernel point equivalence, rather than
tests only on rational points.

If the kernel fails actual affine-line constancy, the extracted tuple can be
chosen nonconstant. Otherwise every polynomial coordinate has degree zero, hence
is a base-field scalar. Naturality preserves these scalars on precomposition with
the zero-section retraction, and monicity of the kernel inclusion gives canonical
constancy. No infinitude, perfectness, smoothness or connectedness is required.

This focused adapter does not supply a polynomial presentation for an arbitrary
unipotent group or prove the full published woundness criterion.
