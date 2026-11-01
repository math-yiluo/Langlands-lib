# Coefficient-model hypotheses and gamma-equation uniformity

This internal, derived module supplies algebraic and measure transport for the
matrix-to-rank-one functional-equation comparison. It proves neither the matrix
to Whittaker integral passage nor the resulting fixed-functional gamma equation.
Its provenance is the published coefficient-image construction, quotient
admissibility, and the existing coefficient-model and quotient-measure
uniqueness theorems.

`coefficientModelEvaluation` is evaluation at the identity on the actual
coefficient image. Its pullback along the surjective `modelMap` is the original
functional, as proved by applying the representation's identity law.
`coefficientModel_isFinite` transports finite generation over the actual group
algebra through the module-linear map underlying this surjective intertwiner.

For a representation of full Whittaker type and a nonzero functional,
`coefficientModelFunctionalsEquiv` identifies the model's entire space of
functionals with the original functional space by pullback. Pullback is
injective because `modelMap` is surjective. It is surjective because every
functional of the original representation is a scalar multiple of the specified
functional, and scalar multiples of evaluation supply its preimages.

`coefficientModel_isOfWhittakerType` combines this equivalence, finite generation,
and the published theorem that admissibility descends along a surjective
intertwiner when compact open subgroups are cofinal.
`glCoefficientModel_isOfWhittakerType` supplies that cofinality for the canonical
p-adic general linear group. Thus no irreducibility, finite length, or equivalence
between the original representation and its coefficient image is assumed.
The field and original carrier universes remain independent.

`equalRankGammaFactor_of_equation` and `unequalRankGammaFactor_of_equation`
start with the complete corresponding gamma equation for a fixed nonzero pair
of functionals at `unipotentQuotientHaar`. They construct the quotient-measure
existence and nonzero-functional witnesses required by the gamma-factor
relation. For any compatible quotient measure, the published measure
uniqueness theorem identifies it with the constructed measure. Any other
nonzero functional pair has the same coefficient models by full Whittaker type,
so `EqualRankGammaEquation.congr_model` or
`UnequalRankGammaEquation.congr_model` transports the supplied equation.
The scalar additive measure and the rational gamma function are unchanged.
The continuation, nonvanishing, Fourier-test, block, and reduced-denominator
requirements are inherited from the supplied gamma equation.

Worker 486 named the local canonical topology instance
`matrixComparisonModelsTopology` to permit combined imports with the adjacent
model convergence and star-integrability proofs. Anonymous local instances
also create global declaration names; the former generated name collided
with those modules. This compatibility correction changes no instance body,
mathematical statement or proof.
