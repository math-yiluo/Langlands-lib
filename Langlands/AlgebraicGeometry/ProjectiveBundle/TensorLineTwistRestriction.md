# Source restriction for tensor-line degree-one comparisons

This derived unit works over an arbitrary scheme `S : Scheme.{u}`, a module
sheaf `M` locally free of fixed rank `n + 1`, and a locally free rank-one module
sheaf `N`. It uses the genuine joint frame atlases and the actual local
comparisons of `TensorLineTwistCharts`.

`tensorChart` and `sourceChart` express the existing open-immersion chart maps
with source scheme `RelativeProjectiveSpace U.val.toScheme n` explicit.
`sourceChartTwistIso` is the existing source-atlas degree-one chart comparison,
with that same explicit source scheme. These wrappers keep definitional
conversions small; they do not change any chart map or module comparison.

`tensorChartRestriction` is the actual tensor-atlas restriction map.
`tensorChartRestriction_eq` identifies it with the actual source-atlas
restriction. `sourceTwistRestrictionIso` transports the source degree-one
transition along this equality. Thus its source is the pullback, along the
tensor restriction, of the standard relative degree-one line on the larger
chart, and its target is that standard line on the smaller chart.

`sourceTwistChartIso_hom` and `sourceTwistRestrictionIso_hom` give the canonical
composite morphism formulas. `sourceTwistChartIso_restrict` proves that the
source local comparison commutes with every actual atlas restriction: the
pullback of the larger comparison followed by the transported transition is
the canonical composite-pullback comparison followed by the smaller local
comparison. All scheme maps in this equation are the actual maps constructed
by the joint atlases and their tensor-line scheme isomorphism.

The proof first establishes three generic transport lemmas.
`local_restrict_congr` transports a given restriction equation along an equality
of restriction maps by substituting that equality and simplifying the
canonical pullback-congruence map. `compHom_local_restrict_congr` combines this
with the published composite-pullback restriction lemma;
`compIso_local_restrict_congr` states the same result with isomorphism
composites. The concrete source restriction law follows by the two hom
formulas and the morphism transport lemma, using the published source-atlas
restriction law and the genuine chart equations.

The provenance is derived from `TensorLineTwistCharts`,
`FrameAtlasTwistRestriction`, and canonical pullback congruence and composition.
No new geometric premise or external mathematical assertion is introduced.
This unit proves the source restriction law only. The scalar cancellation for
the tensor degree-one line times the base line, global comparison, and ordinary
large-level representability remain separate obligations.
