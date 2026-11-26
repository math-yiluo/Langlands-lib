# Actual adelic forms and the full original general-linear operator spaces

For any number field and any closed matrix embedding of the general-linear group of
positive matrix size, `generalLinearAutomorphicForm_uniformGrowth` gives one global
height exponent for every enveloping derivative of an original matrix automorphic form.
The constant in the bound may depend on the derivative. Consequently
`uniformGeneralLinearOperatorRealization_eq_top` identifies the uniform-growth realization
with the whole original stable operator space. With the compactness instance for the additive
adele quotient, `uniformCuspidalGeneralLinearOperatorRealization_eq_cuspidal` identifies the
uniform cuspidal realization with the largest original cuspidal realization.
`compactSpace_adeleQuotient` supplies that instance.

For the standard embedding and rank `n > 0`, the module constructs two continuous complex
linear equivalences:

- `canonicalUniformAdelicAutomorphicFormsEquiv` compares the actual uniform adelic forms
  with `Langlands.Automorphic.AutomorphicForms F n`.
- `canonicalCuspidalRealizationAdelicEquiv` compares the largest cuspidal operator
  realization on the original matrix side with the actual uniform cusp forms. It uses
  `adelicConstantTermEnveloping` for stability under the enveloping algebra and takes the
  same additive-quotient compactness instance as the matrix constant terms.

The value formulas identify each map and its inverse with the corresponding restriction of
`finitePlotSmoothGeneralLinearEquiv`. The comparison uses the induced compact-open
function topologies. In the cusp comparison, membership is transported by
`mem_canonicalUniformGeneralLinearAdelicCuspidalForms_iff`, which compares convergent
vanishing along every proper rational parabolic with the original normalized maximal-block
constant terms. The finite, standard infinite compact and enveloping actions on the same
functions are compared by `finitePlotSmoothGeneralLinearEquiv_rightAction`,
`finitePlotSmoothGeneralLinearEquiv_infiniteSubgroupAction` and
`finitePlotSmoothGeneralLinearEquiv_actualEnvelopingAction`.

## Construction

Pull the original matrix form back along the finite plot-smooth function equivalence. Its
open finite stabilizer comes with that carrier. `GeneralLinearGrowthIndependence` transfers
slice growth to the chosen closed embedding and `adelicSliceModerateGrowthStatement` gives
one bound on the whole adelic group. The existing form comparison transfers the infinite
compact and enveloping-centre finiteness conditions. `adelicAutomorphicUniformGrowth`
then gives a common real exponent for all actual enveloping derivatives.
`hasAdelicUniformModerateGrowth_iff` converts it to a natural exponent for the height and
`hasAdelicUniformPolynomialGrowth_iff_generalLinear` transfers the bound to the matrix
operator action. The form equivalence uses this bound to construct the inverse of the
published uniform-form injection. The cusp equivalence uses the published injection from a
cuspidal realization into uniform cusp forms and the all-parabolic comparison to construct
its inverse. Continuity in both directions follows from the ambient equivalence in
`GroupSchemeAmbientCompactOpen` by restriction to the induced subtype topologies.

## Sources

This is a comparison of Library constructions. Borel–Jacquet, *Automorphic forms and
automorphic representations*, §§3.3 and 4.1–4.4 (printed pp. 194–196), gives the
finite-level, slice-growth and cuspidal conditions used on the original function carriers
(`borel-jacquet-1979-automorphic`, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`).
Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series*, I.2.3 and I.2.17,
case `P = G`, gives the common-exponent growth condition and its application to forms
(`moeglin-waldspurger-1995-spectral-decomposition`,
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`, printed pp. 25, 37–39,
SHA-256 `296dcb3e7170bb0c2689cf0c79136a43cd86976df2b4c51f027cf9365f7fe988`).
Getz–Hahn, *An Introduction to Automorphic Representations*, Definition 6.3.1 and
Definition 6.5.1 (printed pp. 161–162 and 167–168), gives the adelic growth bound
and all-parabolic vanishing condition used in the comparison
(`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`).
