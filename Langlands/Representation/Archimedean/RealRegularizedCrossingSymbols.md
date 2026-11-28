# Regularized crossing symbols along affine parameter lines

Fix a central crossing parameter `ν`, a parity `ε` equal to zero or one, and a
nonzero complex slope `b`. The parameter of the real rank-two multiplier is
`ν + b z`. The symbol is the parity-restricted generic multiplier scaled by
`z` if its denominator has a root at the center, with the erased-denominator
formula defining the analytic value there. The normalization divides by the
appropriate power of `b`, so the scaling factor is a power of `z`.

The existing regularized formulas give modewise analyticity at zero and the
reflection symmetry for every `z`. The closed and discrete integer lattice
gives a neighborhood of the center containing no other exceptional parameter.
At nonzero parameters there, the recurrence and the reciprocal identity
follow from the generic formulas. The erased formula satisfies the recurrence
at the center, and continuity extends the reciprocal identity across zero.
The opposite crossing uses `−ν − b z`. The two denominator pole orders sum to
at most one, since an exceptional denominator root is negative. On the
allowed parity class the two symbols multiply near zero to `z` to that sum.

This derives the scalar normalization needed for Taylor coefficients of a
crossing and its cleared inverse from `RealBlockMultiplierNormalization` and
`RealInducedSwapRegularizedFamily`.
