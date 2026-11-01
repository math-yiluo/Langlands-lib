# Fourier regularity of supercuspidal coefficient cutoffs

This is a derived algebraic and representation-theoretic helper for the
supercuspidal matrix functional equation. Its construction uses the actual
matrix group and the actual conjugate unipotent radicals already in the Library.

For square matrices of size `m + 1`, with `m > 0`, a singular matrix has a nonzero
kernel vector. The published `EqualRankFrobenius.exists_lastRow_eq` completes
that vector to the last row of an invertible matrix. Transposing that matrix
provides a right change of basis after which the singular matrix has zero last
column. The inverse transpose of the `(m,1)` upper unipotent radical has identity
first `m` rows. Multiplication therefore fixes the changed matrix. Conjugating
back supplies a proper conjugate radical which fixes the original matrix under
right inverse transpose. This works for every singular matrix, including zero;
`m + 1` is the ambient dimension, not the rank of the singular matrix.

The subgroup is proper because a full standard block parabolic has at most one
block, whereas this shape has two positive blocks. All linear algebra is over an
arbitrary field. No topological assumption is needed for this geometric lemma.

For the supplied compatible topology on a p-adic field and any supplied additive
Haar measure, `supercuspidalCutoffMatrixTest_fourier_singular` now applies the
actual cutoff Fourier-evaluation criterion to that subgroup. Its determinant
norm is one, and the actual Jacquet quotient is zero by `IsSupercuspidal` and
properness. Thus the raw plus Fourier integral vanishes on every singular
matrix. Scalar self-duality is not needed for this vanishing assertion.

With scalar self-duality, `rectangularFourierEquiv_apply` identifies that raw
integral with the actual Schwartz Fourier transform. The original cutoff already
vanishes on singular matrices. The two conclusions establish membership in
`fourierRegularMatrixTests`. Total disconnectedness of the supplied compatible
p-adic topology is obtained from the published `padicLatticeGeometry`, rather
than assumed separately. `supercuspidalFourierRegularCutoff` is the original
complex-linear coefficient-cutoff map restricted to this proved range; it does
not change the underlying test function or its Fourier transform.

The independent universes of the field and representation carrier are retained.
The results apply to dimension `m + 1` for any `m > 0`, in particular the host's
dimension `n + 2`. This is a derived helper, proved from the existing matrix,
Fourier and Jacquet constructions. It establishes no nonzero operator, scalar
gamma factor, extension to arbitrary matrix tests, or functional equation.
