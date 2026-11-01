# Gamma comparison through an actual submodel

This internal derived support is for the rank-one analytic base. It constructs
maps and proves conditional comparisons. It does not prove either closed
two-block analytic base or analytic factor existence.

For a representation `π`, a specified functional `ℓ`, and an actual
subrepresentation `S` of its coefficient-image representation,
`submodelFunctionMap` includes `S` into the ambient equivariant function space
by composing the two subtype inclusions. It is an injective intertwiner.
`submodelEvaluation` evaluates those functions at the identity. Its coefficient
map recovers the identical underlying function because right translation
evaluated at the identity is evaluation at the translating element. Its
coefficient image is therefore contained in the original image. Evaluation is
nonzero when `S` is nonzero, by the published translate-and-evaluate argument
in `ModelGenericSocleProof`.

`gamma_eq_submodel` compares two existing complete p-adic symmetric gamma
certificates against the trivial rank-one test. The nonzero subrepresentation
can be reducible. The proof chooses a nonzero test functional from the smaller
certificate and applies `IsPairGammaFactor.eq_of_model_le` with evaluation on
`S`, the specified original functional, the proved first-model inclusion and
identity inclusion on the test model. This retains the full measure,
functional, continuation and nonvanishing conditions of both certificates.

`gamma_of_submodel_ambient_matrix` additionally takes an actual subrepresentation
`A` of a smooth ambient representation `ρ` and an actual surjective intertwiner
from `A` to `S`. It composes this with the canonical surjection to the coefficient
model of evaluation on `S`. The published p-adic subquotient coefficient theorem
then gives inclusion of that model's bi-smooth coefficients in those of `ρ`.
The published ambient matrix-to-rank-one comparison, full Whittaker type of `S`,
and supplied normalized matrix data on `ρ` give a full gamma certificate for
`S`. The preceding equality theorem identifies its rational expression with
the factor of the separately assumed existing certificate on `π`. Substitution
returns that complete original certificate with the specified expression.

The field, original carrier and ambient carrier universes are independent.
The submodel carrier consists of functions on the field's general linear group
and lies in the field universe. No original-to-model equivalence,
irreducibility of the original or submodel, normalized-generator transport,
or convergence bound is asserted. The normalized polynomials, epsilon unit and
exponent remain data on the actual ambient representation. Existence of the
original gamma certificate is an explicit premise. Supplying actual socle
occurrence, ambient matrix data and original gamma existence remains separate
work.

The provenance is internal: subtype inclusion, the published coefficient-model
construction, nonzero evaluation, subquotient coefficient inclusion, ambient
matrix comparison, and comparison of existing gamma certificates are composed
as described above.
There is no new literal literature assertion.
