# Scalar normalization of actual equal-rank test vectors

Author: Worker 408.

This module supplies an internal scalar normalization construction for the
existing actual equal-rank JPSS coefficient integrals. It imports
`AnalyticStatement` and changes none of its definitions or imported files.
It does not construct compact test functions or prove the existence of a
constant nonzero test integral.

`normalizeEqualRankFirstVector ψ π ℓ c f` is `c⁻¹ • f` in the actual
coefficient image `(coefficientModel π ℓ).toSubmodule`. Thus it retains the
specified representation and specified Whittaker functional. Since that
image is a complex submodule, this is again an actual coefficient-model
vector. The definition is total, including at zero; the normalization
identities explicitly require `c ≠ 0`.

The implemented proofs first check scalar multiplication in the actual
quotient integrand. Induction on the left-unipotent quotient reduces this
identity to the representative formula `equalRankIntegrand_mk`, where it is
associativity of multiplication. `equalRankIntegral_smul_left` then applies
complex linearity of the total Bochner integral. No extra integrability
assumption is needed for that identity. `EqualRankConverges.smul_left`
separately proves preservation of absolute convergence by scalar
multiplication. `equalRankModelIntegral_smul_left` specializes the same
identity to vectors in the actual coefficient images.

`normalizeEqualRankFirstVector_integral` says that, at each spectral
parameter where the original actual integral equals a supplied nonzero
complex number `c`, replacing the first vector by the normalized vector
makes its actual integral equal to one. Its proof is the scalar integral
identity followed by `c⁻¹ * c = 1`.

`hasRationalContinuation_one_of_eq_on_halfPlane` handles the denominator
condition in the existing continuation relation: the denominator of the
constant rational function one is one, its evaluation is one, and a supplied
right half-plane of equality therefore suffices. It works for every natural
number `q`; no uniqueness assertion or assumption `q > 1` is needed.

The two membership lemmas retain the concrete vectors and Schwartz–Bruhat
function as witnesses in the existing `equalRankRationalValues` set.
`one_mem_equalRankRationalValues_of_integral_one` uses a supplied
right half-plane of constant-one integral values.
`one_mem_equalRankRationalValues_of_nonzero_constant` uses a supplied
right half-plane of one fixed nonzero value and explicitly normalizes
the first coefficient vector. Their conclusion is literal membership of
one, not membership in a span.

These results hold over every topological field, every positive rank
`n + 1` including rank one, arbitrary absolute value and quotient measure,
and representation carriers in independent universes. They do not require
Whittaker type because the input vectors already lie in the actual
coefficient images. Every constant-integral identity used in their
hypotheses must still be proved for actual test data by a separate
construction.

The provenance is internal and derived: the definitions and proofs follow
directly from the published coefficient-image module structure, quotient
integral formula, total Bochner scalar linearity and rational continuation
definition. No additional assertion is attributed to the original
literature. The consuming equal-rank construction is described on JPSS
(1983), printed page 393, but that construction is not implemented here.
