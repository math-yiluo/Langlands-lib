# Actual local rational heights through coefficient extension

This module preserves the existing all-test local kernel-rank height
condition on actual rational formal-atlas maps through coefficient extension.
It derives its results from `AtlasRationalHeight`, the actual rational
coefficient-extension construction and `RationalHeightIso`; no new literature
assertion or general base-change theorem for sheaf sections is assumed.

`HasConstantChartHeight.baseChange` takes an actual global tensor map on two
atlases with equal principal covers and its existing signed constant height
certificate. On a test algebra over the extended coefficient ring,
`onChart_baseChange` expresses the new chart map as the original rational chart
map on the restricted test algebra, conjugated by the actual source and target
chart isomorphisms. The old height certificate applies to that restricted test.
The proved `ofGlobal_isoTransport` theorem preserves its local numerator and
denominator kernel ranks. `isoTransport_eq_comp` identifies this transported
tensor with precisely the extended chart tensor.

`HasConstantChartHeight.reAlgebra` eliminates equality of scalar structures and
retains the height certificate for the same scalar-retyped tensor.
`baseChangeAlong` combines coefficient extension with this transport to the
supplied target algebra structure. Scalar maps may merge generators; no flatness
or injectivity hypothesis is imposed. The proof keeps the actual chart
isomorphisms and does not identify independently selected original charts.

`baseChangedLocalQuasiIsogeny` applies the existing local construction to the
extended tensor and its proved height certificate. It takes nonvanishing of the
distinguished scalar in the rational field and actual scalar divisibility of
both extended test-chart formal modules. Its value is exactly the section of
the specified extended tensor, as the definitional value equation states.
`baseChangedLocalQuasiIsogeny_height` gives that same local section the original
signed constant height. This uses the existing implication from the local
rank condition and scalar divisibility to a genuine local quasi-isogeny; it
does not infer invertibility from a numerical height assignment alone.

The parameters are arbitrary commutative rings `O`, `R`, `S`, a field `F` over
`O`, finite coordinate types, actual atlases with equal covers and a rational
tensor map between them. `R`, `S`, `F` and the test algebras share universe `v`;
`O` may be in universe `u`. Principal covers need not be finite. The height
parameters `π`, the natural rank base `q` and the signed integer `n` are retained.
Actual framed Nilp-base extension is `DrinfeldFramedAtlas.baseChange` in
`DrinfeldFramedBaseChange`; preservation of its framing square remains separate.
