# Compact and finite-order Fourier symmetries

This internal helper applies the actual left-right Fourier change of variables
to invariant Schwartz–Bruhat tests. It does not construct compact-averaged
coefficients, prove Whittaker convergence or perform the block-zero extraction.

`rectangularLeftInvariantTests J` is the complex submodule of actual rectangular
Schwartz tests fixed by left multiplication by every element of `J`. Its
membership theorem is the pointwise formula `Φ(gY) = Φ(Y)`.

The determinant-norm lemmas use the published residue-normalized character:

- `determinantNorm_eq_one_of_mem_compact` specializes the existing theorem that
  a continuous positive character is trivial on a compact subgroup.
- `determinantNorm_eq_one_of_pow_eq_one` applies the norm character to a
  supplied finite-order relation and uses the absence of nontrivial finite
  order in the positive reals.
- `determinantNorm_permutation` uses the finite order of the permutation and
  the actual permutation-matrix homomorphism. The long Weyl result specializes
  this to the reversing permutation, in every rank.
- `determinantNorm_signDiagonal` applies the finite-order result to the
  published actual unit diagonal when every supplied entry has square one.

These norm identities discharge the hypotheses of
`padicRectangularLeftRight_measurePreserving` for compact-subgroup elements,
permutation matrices and sign diagonals. That theorem preserves every actual
rectangular additive Haar measure, so it does not rescale the supplied measure.

`padicMatrixFourierPair_leftRight_invariant` proves that a test symmetry
`Φ(AYB) = Φ(Y)` transfers to
`ΦHat(A⁻ᵀXB⁻ᵀ) = ΦHat(X)` whenever both determinant norms are one. It rewrites
the supplied Fourier-pair identity on both sides and applies the actual
no-scalar change of variables. It uses exactly the given scalar Haar measure
and character.

`padicMatrixFourierPair_compact_left_invariant` packages this for a compact
matrix subgroup `J`. The Fourier partner belongs to
`rectangularLeftInvariantTests` for the actual subgroup image of `J` under
inverse transpose. The proof obtains determinant norm one from compactness,
takes the right matrix to be the identity, and uses a preimage of each element
of the subgroup image. The subgroup need not be open; no irreducibility,
self-duality or exponent normalization is assumed.

The provenance is internal derivation from
`RankOneMatrixFunctionalEquationComparisonFourierTransport`, the existing
compact positive-character theorem, the published norm character and actual
matrix homomorphisms. No original-source analytic result or unproved
covariance statement is used.
