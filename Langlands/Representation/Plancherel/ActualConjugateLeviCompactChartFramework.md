# Compact charts, weak continuity and dense coefficient agreement

Module `Langlands.Representation.Plancherel.ActualConjugateLeviCompactChartFramework`.

## Locally finite families

`IsLocallyFiniteFamily` (from `ActualCommonLeviCoherenceReduction`) is closed
under constants (`isLocallyFiniteFamily_const`), pre- and postcomposition with
fixed linear maps (`IsLocallyFiniteFamily.precomp`, `.postcomp`) and
reindexing along continuous maps (`IsLocallyFiniteFamily.comp_continuous`).

## Dense coefficient agreement

`eq_of_coefficient_dense`: two families of linear maps between parameter
dependent carriers agree everywhere when both preserve given coefficient
maps, the second is surjective at each parameter, the source coefficient map
is injective on a dense set of parameters, and both families are weakly
continuous in fixed charts. At an injective parameter the coefficient identity
forces equality; weak continuity extends it by
`IsWeaklyContinuousFamily.eq_of_eqOn_dense`.

`eq_of_chain` applies this argument when the first family is the composite
of two locally finite families followed by a chart-constant transport.
`chartValue_comp` expresses the composite in fixed charts, and
`IsLocallyFiniteFamily.comp_weaklyContinuous` applied twice gives weak
continuity of the composite. `eq_self_of_loop` uses the same dense
agreement criterion for a translation, a locally finite continuation, and
a return transport, with the two outer maps constant in the charts.

## Fixed compact charts

`compactEval` reads a vector of the fixed compact carrier
`ActualCommonLeviCompactTensor.compactFiber` at a point of `K × K` through
`ActualCommonLeviV3.compactProductTensorEquiv`; it is injective
(`compactEval_injective`), and `compactEval_compactTensorEquiv` identifies it
with the untwisted value of a section of the actual coefficient fiber, using
`compactProductTensorEquiv_compactTensorEquiv` and
`compactProductRestriction_eval`.

`compactValue_const_of_eval`: a family of maps between actual coefficient
fibers whose untwisted values are a fixed value map applied at the left
translate by a point `g ∈ K` has the same value in the fixed compact charts
at all parameters. Since `(g, g)⁻¹ k` lies in `K × K`, the chart value at `k`
is the fixed value map applied to the source chart value at `(g, g)⁻¹ k`.

This is the regularity input in the compact pictures of Waldspurger, *La
formule de Plancherel pour les groupes p-adiques* (2003), IV.1, printed
pp. 276–277, used for the comparisons of V.3, printed p. 295.
