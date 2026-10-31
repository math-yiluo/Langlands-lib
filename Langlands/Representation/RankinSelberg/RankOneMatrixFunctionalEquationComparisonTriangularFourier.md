# Fourier duality for the explicit triangular affine slices

Author: Worker 623.

This internal specialization of complementary affine matrix Fourier inversion
keeps the supplied scalar Haar measure and both character phases explicit.
The field is locally compact, Hausdorff and totally disconnected with its
Borel measurable space. The supplied scalar Haar measure is sigma finite
and self dual for the supplied continuous nontrivial unitary additive
character. The matrix size is `n+1`; `n=0` is also allowed.

In row `i`, `shiftedLowerSliceColumns n i` selects the entry in column zero
when `i=n`, together with the entries in columns `0<j≤i`.
`negativeSuperdiagonal n` has `-1` at `(i,i+1)` and zero elsewhere.
`trailingIdentity n` is diagonal with first entry zero and remaining entries
one. These definitions specify two actual nested product slice measures:

- `shiftedLowerSliceMeasure ν n` puts the supplied scalar Haar measure on
  the selected entries and fixes the others at the negative superdiagonal.
  Thus the first column is zero except for its free final entry; there is
  `-1` on the superdiagonal, zero above it, and free entries on and below
  the diagonal in columns after the first.
- `upperFirstColumnSliceMeasure ν n` puts that same scalar Haar measure on
  the complementary entries and fixes the others at the trailing identity.
  The strictly upper entries and the first column except its final entry
  are free. The first column's final entry and the strictly lower entries
  in the other columns are zero; the trailing diagonal is one.

Writing `Φhat` for the actual plus rectangular Fourier integral,
`shiftedTriangular_fourier_duality` proves both absolute convergence and

```text
∫ Φhat(Y) ψ(-sum_(i=0,...,n-1) Y_(i+1,i+1)) d(shiftedLowerSlice)(Y)
  = ∫ Φ(X) ψ(-sum_(i=0,...,n-1) X_(i,i+1)) d(upperFirstColumnSlice)(X).
```

For `n=0`, the left slice has its single matrix entry free, while the
right slice fixes that entry at zero. Both phases are one. No new measure normalization or scalar factor appears.

The proof verifies that the negative trailing identity is supported in the
selected entries and the negative superdiagonal in their complement. The
entry pairing with those matrices is respectively the negative sum of the
trailing diagonal and of the superdiagonal. Substitution into
`rectangularCoordinateSlice_fourier_duality` gives the result. Its provenance
is internal: it is a sparse-matrix calculation and specialization of the
preceding actual affine-slice Fourier theorem. It asserts no equality of
Whittaker pushforwards, matrix zeta convergence, same-vector block extraction
or gamma functional equation.
