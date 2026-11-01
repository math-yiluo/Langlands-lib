# Conjugate coefficient smoothing and bilinear transfer

This internal helper derives a compact transfer identity from the existing
supercuspidal matrix smoothing and actual algebraic integrated action. It
assumes no functional equation.

The conjugate group test is the pointwise complex conjugate of the compact
determinant norm one coefficient cutoff. Conjugate matrix smoothing means
conjugating the smoothing of the conjugate input test. Scalar evaluation of
the actual integrated action and conjugation of Bochner integration identify
this with integration of the inverted conjugate group test. Conjugation
preserves the existing Fourier-regular test space, so the new smoothing
regularizes every matrix input under the original smoothing hypotheses.

For any complex module W and bilinear pairing B on full matrix tests and
representation vectors, assume that right translation by a determinant norm
one element g transfers to the vector action of rho(g inverse). Then the
pairing of the compactly smoothed test with w equals B of the original test
with the actual integrated rho action of the group cutoff on w. The proof
commutes the two linear maps with finite-fiber integration, changes variables
by Haar-preserving inversion, and applies the translation law on the cutoff
support. It needs no topology on either vector space and no analytic Fubini
argument. Specializing to the conjugate coefficient gives the same integrated
output for every pairing satisfying this translation law.

This file does not establish the translation law for continued zeta pairings,
the spanning of these integrated outputs, or the full functional equation.
