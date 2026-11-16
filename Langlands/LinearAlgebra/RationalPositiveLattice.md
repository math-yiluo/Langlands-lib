# Bounded sets in a lattice with a rational positive form

This internal algebraic helper is derived for the proof of finiteness of actual
integral polarized automorphisms. Its definition and lemmas are internal
constructions, proved algebraically from Mathlib's integral matrix result.

`Langlands.rationalBilinearBall B r` is the set of vectors `x` for which
`B x x ≤ r`, where `B` is a rational-valued integral bilinear form and `r` is a
rational number. The definition requires neither symmetry nor positivity.

For a finite integral basis and a symmetric rational-valued integral bilinear
form which is strictly positive on every nonzero vector, the set where its
diagonal value is at most a prescribed rational number is finite.
`finite_rational_bilinear_le_of_basis` proves this for a supplied finite basis;
`finite_rational_bilinear_le` specializes it to a finite free integral module.
Finite freeness and strict positivity are explicit hypotheses of these helpers.
They do not supply those hypotheses for geometric endomorphism groups or prove
polarized-automorphism finiteness by themselves.

The proof clears denominators in the finite Gram matrix. Multiplication by the
square of the nonzero common denominator produces an integral positive definite
matrix. Its quadratic value is the same positive rational multiple of the
original form. Mathlib's
`Matrix.PosDef.finite_setOfPred_dotProduct_mulVec_le` proves finiteness for the
resulting integral bound, rounded up. The basis coordinate equivalence transports
this result to the original module.
