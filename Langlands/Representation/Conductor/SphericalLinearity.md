# Linearity of the actual spherical coefficients and finite numerators

This internal unit proves linearity in the actual Whittaker model vector
through the constructions of `SphericalSeries`, `SphericalProduct` and
`SphericalEvaluation`. It constructs the subspace of finite numerators.
It does not establish that this subspace is an ideal or that it contains one.

The results are direct deductions from the imported constructions, finite
sum identities and scalar integration. There is no new literature input.
In particular, the unit supplies an algebraic prerequisite for an
essential-vector argument, rather than invoking an essential-vector theorem.

## Finite sums and cancellation

For a commutative ring `A`, `finiteLaurentCoefficientSum S hS` sums the
coefficients of a Laurent series `S` over its finite actual support.
`finiteLaurentCoefficientSum_eq_sum_of_support_subset` proves that the
same sum can be taken over any finite superset of that support: all added
coefficients are zero.

`finiteLaurentCoefficientSum_add` takes the two summands' finite supports
and any proof of finite support for their sum. It proves additivity by
summing over the union of the original supports. Coefficients that cancel
are allowed; no equality between the support of the sum and that union is
assumed.

If `R` is a semiring and `A` is an `R`-module,
`finiteLaurentCoefficientSum_smul` proves scalar compatibility. It sums
over the support of the original series, which contains the support of
the scalar multiple. This includes zero scalars.
`finiteSupportLaurentSubmodule` is the `R`-submodule of Laurent series
with finite actual support. `finiteLaurentCoefficientSumLinearMap`
bundles summation as a linear map from this submodule to `A`.

## Actual integrands and integrated coefficients

`degreeCorankOnePolynomialIntegrandLinearMap` is a complex linear map
from `WhittakerFunctions ψ (n+1)` to functions on the actual left
unipotent quotient with values in the symmetric Laurent algebra. Its
value is the previously defined degree integrand. Linearity is proved
pointwise: the degree cutoff is independent of the Whittaker function,
and on its nonzero branch the function is multiplied by a fixed
determinant weight and spherical Whittaker polynomial. Quotient induction
reduces this assertion to the actual matrix formula.

For the model application, the field `F : Type uF` is an arbitrary
nonarchimedean local field. The complex representation of `GL_(n+2)(F)`
has carrier `V : Type uV` in an independent universe and is assumed smooth.
The Whittaker functional, Jacquet normalization, measures and measurable
and Borel structures are those of the imported model-coefficient
construction. No irreducibility or admissibility assumption is needed.
All vectors belong to the actual `coefficientModel π ℓ`.

`degreeCorankOneModelIntegrand_evaluation_integrable` obtains
integrability of every unit-tuple evaluation from the proved scalar
integrability of the actual model degree integrand. The evaluation map
is composed with the inclusion of the integrand's value span; no
integrability hypothesis is added.

`degreeCorankOneModelCoefficient_add` and
`degreeCorankOneModelCoefficient_smul` compare symmetric Laurent
coefficients by their evaluations on all tuples of complex units.
The imported coefficient-evaluation identity turns each evaluation into
an actual scalar quotient integral. Pointwise integrand linearity,
the preceding integrability result, integral additivity and scalar
compatibility then give equality. Separation by unit-tuple evaluations
returns equality in the symmetric Laurent algebra. This avoids imposing
an extra topology on that algebra or identifying independently chosen
bases of the different integrands' finite value spans.

`degreeCorankOneModelCoefficientLinearMap` bundles the resulting linear
map for each integer degree.

## Series, products and finite numerators

`corankOneModelLaurentSeries_add` and
`corankOneModelLaurentSeries_smul` follow coefficientwise from the
integrated-coefficient results.
`corankOneModelLaurentSeriesLinearMap` bundles these identities for the
actual lower-bounded Laurent series. No finite-support assertion is
required.

For an arbitrary fixed `P : Polynomial ℂ`,
`corankOneModelDenominatorProduct_add`,
`corankOneModelDenominatorProduct_smul` and
`corankOneModelDenominatorProductLinearMap` give the corresponding
linearity after multiplication by the actual coordinate denominator
polynomial. Additivity uses distributivity of multiplication; scalar
compatibility uses the finite coefficient convolution formula. No
condition on the constant coefficient or roots of `P` is imposed.

`corankOneFiniteSupportModelVectors h π hπ ℓ P` is the submodule of model
vectors whose actual denominator product has finite support. Its zero,
addition and scalar closure follow from the product linearity and the
support inclusions for addition and scalar multiplication.
This definition does not assert that every model vector belongs.

`corankOneModelNumeratorLinearMap` maps this submodule to the symmetric
Laurent algebra by the previously constructed
`corankOneModelNumerator`, namely the finite sum of the actual product
coefficients. Its linearity uses the finite-sum identities above.
The application theorem identifies its value with that actual numerator.

`corankOneModelNumeratorSubmodule` is the range of this linear map.
`mem_corankOneModelNumeratorSubmodule_iff` characterizes membership as
the existence of an actual model vector, a proof that its denominator
product has finite support, and equality with its constructed numerator.
Thus the subspace consists exactly of the finite numerators, rather than
their abstract linear span or an arbitrary replacement family.

## Retained obligations

Finite support of the denominator product for every model vector remains
unproved. The construction does not assert existence of an L-polynomial,
an analytic functional equation, an upper degree bound or a comparison
between the formal series and an analytic zeta integral.

Multiplicative stability of the numerator subspace, the absence of common
zeros, the production of the constant numerator one, actual spherical
realization, the essential identity and uniqueness, conductor conclusions
and the exact `EssentialConductorStatement` remain separate obligations.
None is added as a premise of these results.
