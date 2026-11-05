# Spectral entry bounds when actual rational matrices span

Author: Worker 1296.

`MatrixRepresentation.HasFullRationalMatrixSpan` says that the base-field
linear span of the matrices of every actual rational point is the whole
matrix algebra. The points and matrices are the existing `rationalPoints`
and `MatrixRepresentation.rationalMatrix` of the actual group scheme.

Integral characteristic-polynomial coefficients imply integral traces.
For a nonempty index set the trace is the negative of the coefficient of
degree one below the matrix size, and a valuation is unchanged by negation.
For the empty index set the trace is zero. The representation's
multiplicativity then gives integral traces of products of any two actual
rational-point matrices.

`hasUniformlyBoundedEntries_of_fullSpan` applies the published
`exists_valuative_bound_entries_of_trace_vle_one`, using the rational
matrices both as tested matrices and as probes. It gives one nonzero field
element bounding all entries uniformly over all rational points.

This is the trace-duality step in the proof of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Lemma 2.2.11, printed
pp.72–73 / PDF pp.103–104, derived here using the published trace-probe
helper. The result works over any valuatively related field in arbitrary
universe, including positive characteristic, trivial valuations and size
zero. It assumes the full-span condition and supplies no proof of that
condition, semisimplification, finite-kernel reduction, or the full
`ReductiveSpectralBoundednessStatement`.
