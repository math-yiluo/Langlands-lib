# Actual chart maps of supported coefficient complexes

This internal construction makes the actual chart extension and restriction
maps into natural chain maps for the supported coefficient complexes on the
induced rational spectrum. Individual charts need not be preserved by the full
operator group. These chain maps therefore live in modules after forgetting
that action.

## Inputs and coefficients

The complete ultrametric field, presented strict affinoid algebra, topological
group, rational spectral action and varying-open-subgroup transport object
are exactly those of `InducedRationalCompactComplex`. Coefficients are smooth
representations over an arbitrary commutative ring, without a topology on their
modules. Field, group, coefficient-ring, coefficient-carrier and indexing
universes are independent. All function modules have carrier universe
`max u v w`, and the complex shape is arbitrary.

## Construction

`supportedModuleFunctor` forgets the action of the already constructed smooth
supported coefficient functor. `chartCoefficientFunctor` takes locally constant
functions on the actual compact clopen chart, with coefficient maps acting
pointwise. Both are additive. The extension and restriction natural
transformations use the actual linear zero extension and subtype restriction.
Coefficient naturality of extension is the previously proved pointwise law;
restriction naturality is a pointwise equality. Restriction after extension is
the identity.

`mapHomologicalComplex` constructs `supportedModuleComplexFunctor` and
`chartComplexFunctor`. The former is definitionally the previously constructed
supported smooth complex followed by forgetting its action, as recorded in
`supportedModuleComplexFunctor_eq`. Their differential is the coefficient
differential applied pointwise. Prolonging the natural transformations gives
`chartComplexExtension` and `chartComplexRestriction`; their chain equations
are coefficient naturality. The retraction law prolongs to complexes.

`chartComplexProjection` is restriction followed by zero extension. Its
component in degree `i` is exactly the prior `chartPart` linear projection.
Consequently it is idempotent, and projections for distinct actual coset
components are orthogonal. Any finite set containing the nonzero component
support of a degree vector reconstructs that vector by summing these chain
projections. The proved finiteness of that support gives such a finite set
for every vector in every degree. No single finite set for all vectors or all
degrees is asserted.

## Provenance and remaining obligations

The construction is derived from the actual induced rational compact charts,
the full supported-function modules and their chart maps, the supported
coefficient-complex construction, and pinned Mathlib's additive prolongation.
The retraction, projection and finite-reconstruction proofs reduce to the
implemented function-level equalities. No new original-literature assertion
is added. The supplied input coefficient complex is not asserted to be a
geometric or Godement resolution. Analytic and etale sheaf comparisons,
derived compact-support comparisons, arithmetic coefficients, towers and
Harris specialization remain separate obligations.
