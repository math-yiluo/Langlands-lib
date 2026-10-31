# Left-right Fourier transport for the matrix comparison

This internal derived helper proves actual changes of variables for the plus
entry pairing used by `GodementJacquet.MatrixFourierPair`. It does not prove the
matrix-to-Whittaker analytic passage or the final matrix-to-rank-one comparison.

The algebraic lemmas show that transposition preserves the rectangular entry
pairing and that multiplying either argument by a matrix moves its transpose
to the other argument. Their proofs use finite sums and matrix multiplication.
The left multiplication identity also uses the transpose identity and the right
multiplication identity.

`rectangularLeftRightHomeomorph A B` is the actual map `Y ↦ A Y B`, with inverse
`Z ↦ A⁻¹ Z B⁻¹`. `rectangularLeftRightTranslate` pulls Schwartz–Bruhat tests back
along this homeomorphism. Its formula and preservation of the test space are
part of the construction.

`rectangularFourierIntegral_leftRight` assumes an exact pushforward equality
`(Y ↦ A Y B)₊ μ = c μ` for the supplied scalar product measure `μ`. It proves
that the Fourier transform of `Y ↦ Φ(A Y B)` at `X` equals `c` times the Fourier
transform of `Φ` at `A⁻ᵀ X B⁻ᵀ`. The proof applies the measurable embedding
change-of-variables theorem to the above homeomorphism and then computes the
pairing. It applies to arbitrary complex-valued functions; the Bochner integral
convention makes no additional integrability assumption necessary.

`padicRectangularLeftRight_measurePreserving` specializes the published
`padicRectangularHaarScaling` theorem to matrices whose residue-normalized
determinant norms are one. It proves preservation of every Borel additive Haar
measure on the rectangular space, with no scalar normalization chosen, and also
covers zero rows or columns. The right matrix is entered as an inverse in the
published scaling theorem so that the resulting map is exactly `Y ↦ A Y B`.

`padicRectangularFourierIntegral_leftRight` applies this to the product of the
supplied scalar Haar measure. The factor is exactly one. It requires neither an
exponent-zero normalization of the character nor a replacement of the measure.

Finally, `GodementJacquet.padicMatrixFourierPair_leftRight` transports a supplied
pair `(Φ, ΦHat)` to the pair
`(Y ↦ Φ(A Y B), X ↦ ΦHat(A⁻ᵀ X B⁻ᵀ))`. The transformed functions are actual
Schwartz–Bruhat tests. Integrability at every full matrix follows from their
compact support and continuity of the supplied character; the integral identity
is the preceding change of variables. These results hold for every supplied
topological data on every p-adic field, in every rank, and every supplied
`UnitaryAdditiveCharacter`, whose type includes continuity and nontriviality.
No self-duality or exponent-zero normalization is required. Thus they apply in
particular to the same self-dual measure and arbitrary nontrivial character of
the comparison task.

The provenance is internal derivation from the published rectangular pairing,
raw Fourier integral, test-function pullback, determinant Haar scaling, and
Mathlib's measurable embedding change of variables. No original-source analytic
result or unproved Fourier covariance statement is used.
