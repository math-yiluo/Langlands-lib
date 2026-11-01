# Strict atlases of actual line bundles

This is a derived construction from `CommonSourceCocycle`,
`CommonSourceTransitionTransport`, `LineBundleOpenCoverGluing`,
`OpenPairLineBundleGluing` and `StrictCocycleAtlas`. It constructs a line bundle
on the open region covered by a compatible partial atlas and recovers the
specified actual ambient transition isomorphisms. It does not prove the general
open-immersion extension theorem.

A `LineBundleChartFamily X` is a small family, indexed by a type in the same
universe as `X`, of open immersions to `X`, with an actual Library line bundle
on each source. `Transition i j` is the type of isomorphisms between the two
module-sheaf pullbacks on the scheme fiber product over `X`.
`factor_condition` uses monicity to deduce equality over a common source from
equality of the composites to `X`.

`CommonSource A` records a scheme mapping monomorphically to `X`, one actual
module on that scheme, factors of each selected chart through it, and actual
pullback identifications with the chart bundles. The common module need not be
locally free and its map to `X` need not be an open immersion.
`CommonSource.transition` constructs the actual ambient transitions using the
published common-source comparison. `TripleSource i j k` records the same
data just for three charts; `first`, `second` and `third` are its induced
transitions. `TripleCompatible` asserts the existence of such a witness
recovering all three given transitions exactly. This is a sufficient
compatibility predicate, with no assertion that every ordinary cocycle has
such a witness. `CommonSource.tripleCompatible` constructs these witnesses
from any common source, including repeated indices.

`region A` is the supremum of the selected open images. `factor` factors each
selected chart through this open subscheme. Its composite with the inclusion
is the original map, and it is an open immersion. `regionCover` is an actual
scheme open cover of this region: membership in the supremum exhibits an
original chart and a preimage, and the factorization equality gives a preimage
in the region. These constructions also allow an empty selection.

`regionTransition` transports an ambient transition to the overlap over the
region using `OpenUnion.overlap`. The two overlap schemes are genuinely
isomorphic, with unchanged projections. `regionTransition_transition` uses
`transport_transition` to show that an induced transition becomes the transition
from the same common module on the region overlap. `factor_overlap` gives the
ambient equality on this overlap. For each triple witness, `region_cocycle`
rewrites its three transported transitions to common-source transitions and
applies `transition_cocycle`. The result is the precise
`OpenCoverModuleGluing.CocycleCondition`, including repeated indices, with its
canonical square comparisons on the actual triple fiber product.

`gluingData` combines these bundles, transported transitions and the proved
cocycle. `glue` is the actual line bundle constructed by the published
`LineBundleGluingData.glue`; the rank-one proof and chart comparisons come
from that construction. `realization` records this glued module as a
`CommonSource` over the open inclusion, with the canonical chart factors and
the gluing comparisons.

`gluingData_transition` proves that the transitions induced by these comparisons
on the region overlaps equal the prescribed transported transitions. The proof
cancels the invertible pullback of the first comparison and uses
`moduleIso_compatible`; the remaining maps are exactly the canonical square
comparison and the second pulled-back comparison.
`regionTransition_injective` follows from `transport_injective`, since the
map between the overlaps is a scheme isomorphism. Consequently
`realization_transition` recovers every original ambient transition as an
equality of actual isomorphisms, not merely an isomorphism class.

`AtlasLabel` and `GoodAtlas` specialize the published strict label-set atlas
to this family and its triple-witness predicate. `atlasRealization` realizes
its selected transition family, and `atlasRealization_transition` retains each
selected transition label exactly. The abstract chain-union and Zorn results
are available from `StrictCocycleAtlas`; this module does not yet prove any
geometric enlargement or that a maximal atlas covers `X`.

All schemes have arbitrary universe `u`. No Noetherianity, factoriality,
separatedness, integrality or compactness is assumed here. Local extension,
strict enlargement at a missing point, and coverage of a maximal atlas remain
separate obligations for `OpenImmersionLineBundleExtensionStatement`.
