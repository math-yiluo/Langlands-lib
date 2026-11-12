# The enveloping action on cusp forms, given constant-term preservation

This module derives consequences of the target statement
`AdelicConstantTermEnvelopingStatement` (module
`GroupSchemeConstantTermEnvelopingStatement`). That statement says actual
enveloping derivatives preserve identically vanishing normalized constant terms
along a proper rational parabolic. Every result here takes the statement as an
explicit hypothesis `hCT`. Nothing here proves it.

## General groups

Fix a number field `F` and an affine group scheme `G` over `F`, locally of
finite type and smooth of relative dimension `d` (`hsmooth`). Fix also the
commutator premise `hcalc`, the parabolic dynamic statement `hPD`, connected
reductivity `hG`, and `hCT`.

- `normalizedParabolicCuspidal_actualEnvelopingAction`: the actual enveloping
  action preserves the published parabolic cusp condition
  `normalizedParabolicCuspidalSubrepresentation`. Both sides are rewritten with
  `mem_normalizedParabolicCuspidalSubrepresentation_iff`, and `hCT` is applied
  to each proper rational parabolic.
- `actualAdelicEnvelopingAction_mem_uniformAdelicCuspidal`: for a specified
  infinite subgroup `Kinf`, closed embedding `rho` and `0 < N`, the actual
  enveloping action preserves the published uniform cusp forms
  `uniformAdelicCuspidalSubrepresentation`. The form and uniform-growth parts
  are the published `actualAdelicEnvelopingAction_mem_uniformAutomorphic`.
- `uniformAdelicCuspidalEnvelopingAction`: the resulting restriction of the
  actual algebra homomorphism to the uniform cusp forms.
- `uniformAdelicCuspidalInfiniteSubrepresentation_envelopingAction`: on the
  uniform cusp forms, the `Kinf` action of `GroupSchemeInfiniteTranslation`
  and this enveloping action satisfy `R(k) D_a = D_(Ad(k) a) R(k)`. With the
  published finite-adelic action, this gives the uniform cusp forms the
  actions of Getz–Hahn (6.14), printed p. 164, for the infinite subgroup
  `Kinf`.

## General linear groups

For `GL_n` over `F`, all group-scheme hypotheses are discharged by published
results:

- `hsmooth` is `(isConnectedReductive_generalLinear F (Fin n)).smoothDimension_spec`;
- `hcalc` is `adelicDifferentialCommutator_of_smooth`;
- `hPD` is `parabolicDynamic`.

The instance `CompactSpace (AdeleQuotient F)` of the original constant terms is
retained.

- `generalLinearCuspidal_envelopingAction`: every original enveloping
  derivative of a cuspidal original finite-smooth function is cuspidal. The
  function is written as the image of an actual function under
  `finitePlotSmoothGeneralLinearEquiv`, and the enveloping element as the image
  of an actual one under `GeneralLinearGroupPoints.infiniteEnvelopingEquiv`.
  Cuspidality is transported by the published
  `mem_normalizedGeneralLinearParabolicCuspidal_iff`, and the derivative by
  `finitePlotSmoothGeneralLinearEquiv_actualEnvelopingAction`.
- `generalLinearCuspidalFiniteSmoothSubmodule` is the cuspidal subspace of the
  original finite-smooth carrier. It is invariant under the whole concrete
  operator algebra. Finite and standard compact translations preserve it
  because `cuspidalSubrepresentation` is invariant under all adelic right
  translations (published `operator_invariant_iff`).
- `cuspidalGeneralLinearFormSubrepresentation`: the cuspidal forms are an
  invariant subspace of `fullAutomorphicAction`.
  `cuspidalGeneralLinearOperatorRealization` is the corresponding existing
  `OperatorRealization`, through `operatorRealizationFullFormOrderIso`. A
  stable function lies in it exactly when it is cuspidal.
- `le_cuspidalGeneralLinearOperatorRealization_iff`: a realization is contained
  in it exactly when it is cuspidal. So it is the largest cuspidal
  realization, and it is itself cuspidal.
- `uniformCuspidalGeneralLinearOperatorRealization_eq`: the uniform cuspidal
  realization of `GeneralLinearUniformCuspidalRealization` equals the meet of
  the uniform realization and the cuspidal realization. In
  `GeneralLinearUniformCuspidalRealization` the identification with all
  uniform cuspidal functions was left open; here it holds under `hCT`.

## Provenance

The content is internal: it consists of conditional consequences of a
published target statement, derived from published Library constructions.
They are the uniform form and cusp form spaces with their enveloping actions,
the `GL_n` function and enveloping comparisons, the all-parabolic cusp
comparison, the operator realization framework,
`GroupSchemeInfiniteTranslation` and `GeneralLinearUniformCuspidalRealization`.
Getz–Hahn is cited for the module structure (6.14) and for cusp forms,
Definition 6.5.1 (printed p. 166).

## Scope

The statement `hCT` is a hypothesis; it has its own proof target. The module
does not prove uniform growth of all forms or admissibility, and it constructs
no cuspidal realization beyond the largest one.
