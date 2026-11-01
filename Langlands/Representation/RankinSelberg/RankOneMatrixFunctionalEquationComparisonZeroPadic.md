# The full p-adic rank-one comparison

This derived module completes the `n = 0` branch of the conditional
matrix-to-rank-one gamma comparison. It does not address positive rank.
Its inputs are the actual full Whittaker-type representation, a specified
nonzero functional, and normalized matrix functional-equation data on that
functional's actual coefficient model. The field and original representation
carrier universes are independent.

`rankOneTrivialInverseFunctional` is the identity linear form on the complex
carrier of the trivial rank-one representation. The rank-one unipotent group
is trivial, so every linear form lies in the inverse-character functional
space. Evaluating at one proves this functional is nonzero.

`rankOneMatrixFunctionalEquationComparison_zero` applies the actual
fixed-functional Tate passage from
`RankOneMatrixFunctionalEquationComparisonZero` with the canonical residue
cardinality and absolute value, the supplied additive measure, and
`LocalFactor.residueReflection`. That reflection unit is precisely the
inverse residue cardinality. The theorem uses the original matrix data;
it assumes no separate rationality, convergence, Fourier-pair existence,
irreducibility, finite length, or equivalence with the coefficient model.

The trivial rank-one representation is smooth because every group element
acts identically. The published scalar rank-one Whittaker-type theorem and
standard-to-inverse character adapter give its full inverse Whittaker type.
The published equality `unipotentQuotientHaar_zero` identifies the constructed
quotient measure with the normalized rank-one quotient Haar measure used by
the Tate passage. The gamma uniformity adapter then supplies existence of a
compatible quotient measure and nonzero functionals and transports the entire
equation to every compatible quotient measure and every nonzero functional
pair. Exact measure equality and coefficient-model equality preserve the
same rational gamma expression, supplied scalar measure, full row Fourier
tests, and reduced-denominator domain.

The final step unfolds the published pair and symmetric conventions at
equal rank one. No change of variables or extra scalar is introduced there.
The conditional rank-one argument does not need a self-duality assumption:
the matrix premise already supplies the Fourier witnesses and normalized
equations used by the Tate passage. It therefore applies in particular to
every self-dual measure required by the parent statement.

The provenance is internal composition of the actual Tate-passage and
gamma-uniformity lemmas, with the published canonical normalization and
trivial-quotient comparison. The positive-rank block argument remains a
separate obligation of the parent task.

The local canonical instances have explicit `matrixComparisonZero` names,
with unchanged terms and locality. This prevents generated-name collisions
when the L divisibility and gamma comparison modules share one entry module.
