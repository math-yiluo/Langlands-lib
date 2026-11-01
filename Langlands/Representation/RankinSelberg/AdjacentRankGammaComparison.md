# Adjacent-rank gamma comparison on a nonzero separated integral

This internal prerequisite identifies an existing ambient unequal-rank gamma
factor from fixed normalized equations on the actual separated model
coefficients. It does not yet construct the two block factor certificates or
prove the closed adjacent-rank gamma statement. The field, first-block,
test and ambient carrier universes are independent.

`AdjacentRankSeparatedNormalizedEquations` is a proposition. For each actual
square test `Φ`, row test `φ`, first-block coefficient `W`, and ambient
coefficient `U` whose underlying function is the corresponding separated
model integral, it asks for `AdjacentRankCorankFunctionalEquation` for every
actual test coefficient. The same polynomials `P`, `PD`, units `ζ`, `c` and
integer `m` are used throughout. The supplied self-dual additive Haar and
quotient measure remain fixed.

`adjacentRankImage_gamma_eq_expression_of_separated` assumes full Whittaker
type for the first block, ambient representation and test representation,
specified nonzero ambient and test functionals, and equality of the whole
actual model-map range with the ambient coefficient range. Given an existing
`UnequalRankGammaEquation` with factor `G`, a nonzero dual polynomial `PD`,
the actual test model's minus-one scalar `ζ`, and the preceding separated
equations, it proves

```
G = rationalGammaExpression (LocalFactor.residueReflection F) c m P PD.
```

The image equality is an explicit hypothesis and is not derived by this
module. Neither the first block nor the test representation is assumed
irreducible. Full Whittaker type retains its admissibility, finite generation
and whole functional-line requirements. The conclusion identifies a supplied
gamma equation; it does not independently certify `P` or `PD` as L polynomials.

The proof first converts the scaled-standard test functional to the inverse
character without changing any underlying coefficient function. Uniqueness
of the minus-one scalar, using its nonzero functional, identifies the scalar
in the ambient equation with `ζ`. The ambient equation's nonzero rational
value at zero row/block yields a nonzero corank continuation.
`adjacentRankImage_exists_nonzeroSeparatedContinuation` then selects an
actual separated ambient coefficient and test coefficient with nonzero
corank continuation `R`.

Both the ambient gamma equation and the supplied separated equation apply
to this same pair. At corank one the block Weyl element is the identity:
the second block has dimension one and its long Weyl element is `1`.
`adjacentRank_dualUnequalRankIntegral_eq_corank` consequently identifies the
literal dual zero-block integral with the corank integral of the actual
first and second dual functions. Rational-continuation uniqueness identifies
both original continuations with `R` and the two dual continuations with
each other. `NormalizedFunctionalEquation.gamma_value_of_regular` converts
the normalized equation to the gamma equation with its prescribed rational
expression, using `PD ≠ 0` and the actual residue reflection. Finally
`GammaFunctionalEquation.gamma_unique` cancels the nonzero rational value.
All regularity guards in these predicates are retained; there is no
cancellation on unrestricted bilateral coefficient series.

`adjacentRankImage_gamma_eq_productExpression` supplies the separated
premise from fixed equal-rank equations and
`AdjacentRankMatrixFunctionalEquationWitnesses`. For every row test it
chooses the actual row Fourier partner by `rowFourierCompatibility` and
applies `adjacentRankModel_matchedNormalizedFunctionalEquation`. Its
conclusion uses `P₀ * P₁`, `PD₀ * PD₁`, `c₀ * c₁` and `m₀ + m₁`.
Both dual polynomials must be nonzero. Equal-rank and matrix equations
remain explicit premises; no assertion of their existence for arbitrary
test representations is made here.

The provenance is internal: the proof composes the published zero-block /
corank identity, actual bilinear continuation and tensor-spanning reduction,
matched original/dual finite-product equations, continuation uniqueness,
minus-one scalar uniqueness and gamma uniqueness. It adds no literature
translation or assumption to the existing target statements. Construction
of the fixed block equations and their certified factors, passage through
the genuine irreducible test socle, continuation of the second-block twist
and reversal of the actual ordered induced family remain separate steps.
