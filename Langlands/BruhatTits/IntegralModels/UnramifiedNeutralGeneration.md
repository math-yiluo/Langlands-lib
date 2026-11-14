# Generation of the unramified neutral integral points

The derived theorem `unramifiedNeutralRootCentralizerGroup_eq_neutral` proves
that the actual integral centralizer constructed inside the neutral model,
together with all actual apartment root fixers, generates every neutral
integral point. It assumes a supplied relative-component model whose full
integral points are the character-valuation kernel intersected with the
pointwise fixer of the specified apartment set. The apartment set need not
be bounded or nonempty, and no finite-index premise is used. The universe
parameter is arbitrary.

The construction `unramifiedNeutralRootCentralizerEquiv` is the resulting
multiplicative equivalence between these actual subgroups of rational
points. Its value has the same ambient rational point as its argument, as
recorded by `coe_unramifiedNeutralRootCentralizerEquiv`.

The proof applies `IntegralSplitTorusData.rootCentralizerIntegralPoints_eq`
to the actual integral apartment torus factored through the neutral model.
The maximal-unramified integers are Henselian and have algebraically closed
residue field. Smoothness of the supplied relative component and its
geometrically connected fibres provide the remaining integral hypotheses.
Each generic root intersection is its apartment root fixer by
`rootGroupPoints_inf_unramifiedNeutral_eq_rootFixer`. The generic centralizer
intersection is the image of the constructed integral centralizer by
`centralizerModel_map_integralPoints_eq`. Replacing those generators in the
general generation theorem gives the claimed equality.

This is internal derived content from the actual integral torus, root and
centralizer constructions. It supplies the neutral-generation step toward
KP Theorem 8.3.13; it does not identify the centralizer image with a specified
torus Iwahori subgroup or construct the full fixer model.
