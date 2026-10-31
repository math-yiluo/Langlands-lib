# Actual complementary affine matrix slices

Author: Worker 623.

This internal helper lifts the proved coordinate-slice Fourier identity to
rectangular matrices, with the actual nested product measure on the matrix
entries. The field is locally compact, Hausdorff and totally disconnected,
with its Borel measurable space. The supplied scalar Haar measure is sigma
finite and self dual for the supplied continuous nontrivial unitary additive
character.

`rectangularCoordinateSliceMeasure ν S c` is the product over rows of the
coordinate slice measures: in row `i`, columns in `S i` carry the supplied
scalar Haar measure, and other columns carry Dirac masses at `c i j`.
`rectangularCoordinateMask` applies the row coordinate mask entrywise.
The rectangular pairing is the published sum over all entrywise products,
with no sign or conjugation.

For every Schwartz function on every rectangular matrix space, including
zero dimensions, `rectangularCoordinateSlice_fourier_duality` gives absolute
convergence and the identity

```text
∫ Φhat(Y) ψ(-sum_(j in S_i) A_ij Y_ij) d(slice(S,B))(Y)
  = ∫ Φ(X) ψ(sum_(j outside S_i) B_ij X_ij) d(slice(complement(S),A))(X).
```

Here `Φhat` is the actual plus rectangular Fourier integral with the supplied
nested product of the same scalar Haar measure. No auxiliary Haar measure
or scale factor is chosen.

The proof uses the published finite tensor decomposition, this time with
one Schwartz function on a row per factor. Finite product integration and
the preceding row slice theorem prove the identity and integrability for
one tensor of row functions. Finite linear combinations prove the full
claim. This is internally derived from the published row tensor theorem,
actual rectangular Fourier definitions and the coordinate slice theorem.
It asserts no matrix zeta convergence, Whittaker pushforward comparison,
same-vector paired extraction, or gamma equation.
