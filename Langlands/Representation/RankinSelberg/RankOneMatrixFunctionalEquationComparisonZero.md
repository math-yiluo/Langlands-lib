# The actual equal-rank Tate passage

This internal comparison concerns the rank-one (`n = 0`) branch of the
matrix-to-rank-one functional-equation task. It uses the actual coefficient
model of the supplied functional, the trivial second rank-one representation,
and the same scalar Fourier measure throughout.

`weylLong_rankOne_eq_one` checks the actual unsigned Weyl matrix by its entries.
`rankOneTrivialModel_constant` uses surjectivity of the model map to show every
second model vector is a constant function. A nonzero second functional has
the constant-one function in its image, by the bijectivity of a nonzero linear
form on the complex numbers. This also proves that its model has minus-one
scalar one.

The two integrand comparison lemmas absorb the constant second vector into
the first vector. The original equal-rank integrand then equals the actual
matrix integrand after pulling the row test back along the unique-row
homeomorphism. For the dual integrand, the actual first and second dual
functions have character `ψ.scale (-1)`. At rank one their unsigned long
Weyl element is the identity, so the first function is precisely the actual
`coefficientIota` transform. Both complex shifts are zero. These are
pointwise identities, without convergence assumptions or selected analytic
data.

The two `ModelIntegral_rankOne_eq_matrixIntegral` lemmas use the actual
`rankOneQuotientHaar`, transported from the normalized group Haar measure
because the rank-one unipotent subgroup is trivial. They identify both
totalized integrals. The two corresponding convergence lemmas identify
absolute integrability as well. Thus continuation is transported by equality
of actual functions of the spectral parameter.

`rankOneModelMatrixCoefficient` constructs the actual bi-smooth matrix
coefficient of the model representation obtained by absorbing the constant
second vector. Its membership proof uses the full coefficient-space
identification in `RankOneMatrixFunctionalEquationComparisonZeroCoefficients`;
it assumes full Whittaker type and nonzeroness of the supplied first
functional.

`equalRankGammaEquation_rankOne_of_matrix` assumes actual normalized matrix
functional-equation data for that model representation. For each row test
it pulls back to the full one-by-one matrix space, takes the matrix Fourier
witness supplied by the premise, and transports this witness back to a row
test. The raw Fourier-integral identity from the Fourier helper proves that
the result is the actual plus row Fourier pair, with the same character and
the same scalar measure. No self-dual normalization or character conductor
restriction is added in this conditional step.

The original and inverse-transpose analytic assertions supply continuations
for the constructed coefficient. The matrix equation then applies to exactly
that coefficient and the Fourier-related matrix tests. The proof uses
`NormalizedFunctionalEquation.gamma_value_of_regular`, with nonzeroness of
the dual generator polynomial, to obtain the gamma equation on its entire
reduced-denominator domain, including canceled zeros in the displayed
polynomial expression. It works for every `q > 1` and every unit reflection
scale `δ` satisfying `δ = q⁻¹`.

For the required nonzero continuation, a normalized generator of the matrix
value set supplies a nonzero actual value. The full coefficient-space
equality writes its coefficient as an underlying model function. A
constant-one vector in the second model and the inverse row/matrix test map
then give the same value in the equal-rank family. This proves all clauses
of the fixed-functional rank-one gamma equation at `rankOneQuotientHaar`.
Transport to all nonzero first functionals and compatible quotient measures,
and the positive-rank comparison, remain separate steps.

These calculations implement the rank-one/Tate description of JPS 1979,
printed page 181, directly from published coefficient and integral APIs.
They do not use the source's positive-rank block range.
