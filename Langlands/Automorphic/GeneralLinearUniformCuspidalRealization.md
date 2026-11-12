# Cuspidal operator realizations of `GL_n` and the actual uniform cusp forms

This module continues `GeneralLinearUniformOperatorRealization`. Fix a number
field `F`, a rank `n`, and a matrix representation `rho` of the actual group
scheme `GL_n` over `F`, of dimension `N > 0`. The module compares the existing
`GL_n` operator realizations (`OperatorRealization`,
`CuspidalOperatorRealization`) with the actual group-scheme uniform forms and
uniform cusp forms. These are the forms for the transported standard maximal
compact `generalLinearStandardInfiniteCompact F n`.

## Membership in the uniform realization

`mem_uniformGeneralLinearOperatorRealization_iff`: a function of the stable
space `StableAutomorphicFunctions F n` lies in
`uniformGeneralLinearOperatorRealization F n rho hN` exactly when it satisfies
`IsGeneralLinearUniformGrowth F n rho`. The proof uses the published
`mem_fullFormImage_iff` and the equality of the realization's full-form image
with `uniformGeneralLinearFormSubrepresentation`.

`operatorRealization_toContinuous_eq` records that `S.toContinuous f` is the
underlying function of `f`. This holds by definition.

## Realizations inside the uniform realization

The remaining results take the hypotheses of the published uniform-form
comparison: a smooth atlas `hsmooth`, the scalar-commutator premise `hcalc`, a
closed embedding `hrho`, and connected reductivity `hG`. Let `S` be an
`OperatorRealization F n` with `S ≤ uniformGeneralLinearOperatorRealization F n
rho hN`.

- `uniformRealizationAdelicFormMap hsmooth hcalc hrho hG S hS` is a complex
  linear map from the space of `S` into the actual uniform forms
  `UniformGeneralLinearAdelicForms`. It sends a vector to the inverse image of
  its function under `finitePlotSmoothGeneralLinearEquiv`. Membership in the
  uniform forms is the published criterion
  `mem_uniformAdelicAutomorphic_iff_generalLinear`: the function is an
  original form and has uniform growth by the hypothesis `hS`.
- The matrix function of the image is the realized vector's function
  (`finitePlotSmoothGeneralLinearEquiv_uniformRealizationAdelicFormMap`). The
  published injection `uniformAdelicAutomorphicGeneralLinearMap` returns the
  realized form `S.formInclusion f`.
- The map is injective. It carries the realization's finite operator for
  `GeneralLinearGroupPoints.finiteHomeomorph F n c` to actual finite translation
  by `c`. It carries the realization's differential operator for
  `GeneralLinearGroupPoints.infiniteEnvelopingEquiv F n hsmooth hcalc a` to the
  published actual enveloping action of `a`. Both proofs apply the injectivity
  of `uniformAdelicAutomorphicGeneralLinearMap` and its published intertwining
  lemmas.

## Cuspidal realizations

This part takes the instance `CompactSpace (AdeleQuotient F)`, which the
original constant terms use. The Library proves it as
`Langlands.Global.compactSpace_adeleQuotient`.

`uniformCuspidalGeneralLinearOperatorRealization F n rho hN` is the realization
of all stable functions `f` such that, for every element `a` of the concrete
operator algebra `automorphicOperatorAlgebra F n`, the translate `a·f` has
uniform growth and is cuspidal (`IsCuspidal`, vanishing of all proper
two-block constant terms). It is an invariant subspace because the condition
for `a` applied to `b·f` is the condition for `a*b` applied to `f`. The module
proves the following:

- it is contained in the uniform realization;
- it is cuspidal;
- `le_uniformCuspidalGeneralLinearOperatorRealization_iff`: a realization `S`
  lies in it exactly when `S` lies in the uniform realization and `S` is
  cuspidal. So it is the largest cuspidal realization inside the uniform
  realization.
- `CuspidalOperatorRealization.realization_le_uniformCuspidal_iff`: an
  irreducible cuspidal realization of rank `r + 1` lies in it exactly when it
  lies in the uniform realization.

## The actual uniform cusp forms

This part also takes the published parabolic dynamic statement
`hPD : ParabolicDynamicStatement`, which the Library proves.
`UniformGeneralLinearAdelicCuspidalForms` abbreviates the published actual
uniform cusp forms `uniformAdelicCuspidalSubrepresentation` of `GL_n`. Their
cuspidality is vanishing of the normalized constant term along every proper
rational parabolic.

- `mem_uniformAdelicCuspidal_iff_generalLinear`: an actual function is a
  uniform cusp form exactly when it is a uniform form and its original matrix
  function is cuspidal. The proof uses the published
  `mem_normalizedGeneralLinearParabolicCuspidal_iff`, which compares all
  proper rational parabolics with the standard two-block splittings.
- `uniformRealizationAdelicCuspidalFormMap`: for `S` inside the uniform
  realization and cuspidal, the map above lands in the uniform cusp forms. It
  is injective and has the same underlying function.
- `CuspidalOperatorRealization.uniformAdelicCuspidalForms_ne_bot`: if an
  irreducible cuspidal realization of rank `r + 1` lies in the uniform
  realization, then the actual uniform cusp forms of `GL_{r+1}` are nonzero.
  The proof uses the published nontriviality of the realization's space.

## Provenance

The content is internal: it is derived from published Library constructions.
They are the `GL_n` operator realizations (`OperatorRealization`,
`FullOperatorRealization`, `CuspidalOperatorRealization`), the
uniform-realization module, the group-scheme cusp forms
(`GroupSchemeCuspidalForms`) and the parabolic cusp comparison
(`GeneralLinearParabolicCuspidalEquivalence`). No new external theorem is
used.

## Scope

The module does not prove:

- that every `GL_n` automorphic form has uniform growth. Containment in the
  uniform realization stays an explicit hypothesis.
- that cuspidality is preserved by the enveloping action. Hence it does not
  identify `uniformCuspidalGeneralLinearOperatorRealization` with all uniform
  cuspidal forms, and it gives no map from the actual uniform cusp forms back
  to a cuspidal realization.
- the existence of any cuspidal realization.
- any statement about `L²` spaces, central characters or groups other than
  `GL_n`.
