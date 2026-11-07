# Native coefficient compact-induction coinvariants

This internal construction extends the published complex compact-induction
quotient integral to a native commutative complex algebra `R`. Its entry point is
`Langlands.Induction.Coefficient.compactCoinvariantEquiv`.
The coefficient ring, group and vector carrier have independent universes.

Let `σ : Representation R H V`, where `H` is a subgroup of a topological group
`G`. The additive group `V` carries its given `R`-module and complex-module
structures, with `IsScalarTower ℂ R V`. All compact functions below are the
original covariant functions with a uniform open right stabilizer and compact
support modulo `H`; the group acts by the original right translations.

## Scalar restriction and actual quotients

`compactFunctionsComplexEquiv` retains each function value and its covariance,
smoothness and support certificates when restricting the inducing operators to
complex scalars. `compactInducedComplexEquiv` proves that this map intertwines
right translation.

For any representation `σ` of an arbitrary group, `fullRelations_complex_eq`
identifies the complex span of the relations `σ(g)v - v` with the restriction of
the native `R`-span. The proof first observes that each complex generating
relation lies in the native span. Conversely it proves by span induction that
the complex relation space is stable under each coefficient: multiplying a
generator by `r` gives `σ(g)(r • v) - r • v`; multiplication commutes with complex
scalars. This proves the reverse inclusion by native span induction.

`fullCoinvariantsComplexEquiv` is therefore a complex-linear equivalence between
the complex full quotient and the native full quotient. On original vectors it
sends `[v]` to `[v]`. The native quotient receives its original inherited complex
module structure. `fullCoinvariantsCongr` applies full coinvariants to a complex
representation equivalence, using its two intertwining maps and proving the
inverse laws on representatives. Together these constructions give
`compactCoinvariantsComplexEquiv`, again with its formula on original compact
functions.

## Native integral and descent

For a supplied Borel measure `ν` on the left quotient `H \ G`, finite on compact
sets, `compactCoinvariantIntegral` is an `R`-linear map from the native compact
functions to the native inducing coinvariants. Its underlying map is the
published complex finite-fiber algebraic integral of the original function
values in the inducing coinvariants, followed by `fullCoinvariantsComplexEquiv`.
`compactCoinvariantIntegral_apply` gives this precise formula.

Additivity follows from the complex integral. Coefficient linearity follows by
applying its published naturality to multiplication by `r` on the inducing
carrier. This is a complex intertwiner because the inducing operators are
`R`-linear and the scalar actions commute. On compact functions it acts
pointwise; on quotient classes it is native multiplication by `r`.

When every quotient right translation preserves `ν`,
`compactCoinvariantIntegral_translate` proves invariance of this same integral.
`compactCoinvariantDesc` then descends it through the native ambient full
relation-span quotient. `compactCoinvariantDesc_mk` is its original-function
formula, and `compactCoinvariantDesc_complex` compares it with the published
complex descended integral on every actual quotient class.

## Bijectivity and scope

The bijectivity result assumes that `G` is Hausdorff and locally compact and has
compact open subgroups in every identity neighborhood, and that `H` is closed.
Both groups have supplied Borel measurable structures. The supplied ambient and
subgroup measures are regular two-sided Haar measures; `ν` is Borel, finite on
compact sets, and satisfies `QuotientIntegration.IsCompatible H μG μH ν`.
The inducing representation is smooth. These are the hypotheses of the
published complex `compactCoinvariantIntegralBijective` theorem, now applied to
the restriction of the actual native inducing action.

`compactCoinvariantDesc_bijective` uses
`compactCoinvariantDesc_complex` to express the native map as the composite of
the two scalar-restriction quotient equivalences and that bijective complex
integral. `compactCoinvariantEquiv` packages the resulting bijective native
linear map as
`Representation.Coinvariants (compactInduced H σ) ≃ₗ[R]
Representation.Coinvariants σ`. Its original-function and explicit integral
formulas are proved by `compactCoinvariantEquiv_mk` and
`compactCoinvariantEquiv_mk_integral`.

This is derived from the existing integral, its naturality and its proved
bijectivity, rather than an independently attributed assertion from the
literature. It supplies the coefficient-linear integral core for a later orbit
calculation. No existence of compatible quotient measures, normalization or
normalizer equivariance, rational orbit geometry, geometric filtration or
compact-open fixed-module finiteness is asserted here; these remain separate
obligations for the universal-family Jacquet finiteness theorem.
