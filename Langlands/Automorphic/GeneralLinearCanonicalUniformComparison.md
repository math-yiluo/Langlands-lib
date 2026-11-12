# The `GL_n` uniform comparisons with every hypothesis discharged

The published comparisons `GeneralLinearUniformOperatorRealization` and
`GeneralLinearUniformCuspidalRealization` take the following data as explicit
parameters:

- a matrix representation `rho` and a proof `hrho` that it is a closed embedding;
- `0 < N`;
- a smooth atlas `hsmooth` of a relative dimension `d`;
- the scalar-commutator premise `hcalc`;
- connected reductivity `hG`;
- for cusp forms, the parabolic dynamic statement `hPD`.

This module instantiates all of them for `GL_n` over a number field `F`, rank
`n > 0`. Every parameter except `0 < n` is discharged by a published result:

- `rho` is the published standard representation
  `MatrixRepresentation.standard (Fin n)`. Its dimension is `n`, so `0 < N`
  becomes `0 < n`. `generalLinearStandard_isClosedSubgroup` proves it is a
  closed embedding: its underlying morphism is the identity.
- `hsmooth` is the canonical reductive atlas
  `(isConnectedReductive_generalLinear F (Fin n)).smoothDimension_spec`.
- `hcalc` is `adelicDifferentialCommutator_of_smooth`.
- `hG` is `isConnectedReductive_generalLinear`.
- `hPD` is `parabolicDynamic`.

## Results

- `CanonicalUniformGeneralLinearAdelicForms F n hn` abbreviates the actual
  uniform adelic forms of `GL_n` for this data and the transported standard
  maximal compact.
- `canonicalUniformAdelicAutomorphicRealizationEquiv` is the published linear
  equivalence `uniformAdelicAutomorphicRealizationEquiv`, here between these
  forms and the space of the uniform operator realization
  `uniformGeneralLinearOperatorRealization F n std hn`. It keeps the
  underlying matrix function.
- `CanonicalUniformGeneralLinearAdelicCuspidalForms F n hn` abbreviates the
  actual uniform cusp forms for this data.
  `mem_canonicalUniformGeneralLinearAdelicCuspidalForms_iff` shows that they
  are the uniform forms whose original matrix function is cuspidal. This needs
  the instance `CompactSpace (AdeleQuotient F)` of the original constant terms,
  which the Library proves as `Langlands.Global.compactSpace_adeleQuotient`.
- `canonicalUniformRealizationAdelicCuspidalFormMap` and its injectivity: a
  cuspidal operator realization inside the uniform realization maps
  injectively into these uniform cusp forms.

The intertwining, range and compact-closure results of the published modules
apply to these instances unchanged.

## Provenance

The content is internal: it instantiates published constructions
with published proofs of their hypotheses. No new mathematics is introduced.

## Scope

Rank `0` is excluded, because the standard representation then has dimension
`0`. No independence of the choice of representation is asserted for uniform
growth.
