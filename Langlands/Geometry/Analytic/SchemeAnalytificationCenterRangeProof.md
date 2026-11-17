# Center ranges from principal-open ranges

This module gives internal reductions for the affine-open range clause of
`AnalytificationCenterStatement`. It does not assert the principal analytic
localization-range input.

`CenterRange.localCenter_mem_basicOpen` identifies membership of the local
center in the basic open of a section `g` with nonvanishing of the point's
seminorm on `basicOpenGenerator f U g`. The proof uses the canonical affine
spectrum isomorphism and the compatibility of basic opens with the open
subscheme inclusion.

`CenterRange.BasicOpenRangeData K f` is the explicit input that the range of
restriction from each principal affine open equals the inverse image of that
open under the local center. `range_localMap_basicOpen_of_nonvanishing` converts
a corresponding seminorm nonvanishing-range formula into this input.

Under `BasicOpenRangeData`, `range_ι` proves that the inverse image of every affine
open under the global center is exactly the range of its chart map. To see the
nontrivial inclusion, represent a glued point on some affine open, choose a
principal neighborhood of its center inside the desired open, lift to that
principal chart, and use the quotient's compatibility with restrictions. The
reverse inclusion is the published `center_ι_mem`.

`range_localMap` also assumes the explicit composition identity for analytic
restriction maps. It proves the corresponding range formula for any inclusion
of affine opens by choosing a principal neighborhood in the larger open inside
the smaller one, lifting there, and then composing restrictions.

The paired `AnalytificationCenterComparison` module gives the rational-center
formula and conditional reductions of the singleton rational fibre and scheme
center surjectivity. These reductions use no norm-extension theorem. Their
remaining seminorm injectivity, affine surjectivity, and chart-range inputs are
explicit arguments.

All constructions here are derived from the published center and quotient
formulas and Mathlib's affine principal-open basis. Their role in the literature
is the chart argument in Berkovich's Theorem 3.4.1(i), proof steps (2)–(3) and
Remark 3.4.2, as recorded in the target's published Markdown. No stronger
unconditional theorem is claimed here.
