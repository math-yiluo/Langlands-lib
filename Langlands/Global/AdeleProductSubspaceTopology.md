# The product subspace topology on the original adelic ring

This module constructs the independent coefficient topology appearing in Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011), printed
p.10, Example 4.3: the topology on the original adelic ring induced by its inclusion
in the full product of the completed fields. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

`curvePlaceCompletionProductMap` sends an actual curve-place adele to its original
coordinate family. `curvePlaceProductSubspaceAdeleTopology` pulls back the full
product of the given completed-field topologies along that map. The map is
injective by extensionality of the original restricted product.

`NumberFieldCompletionProduct` consists of every infinite completion and every
finite completion. `numberFieldCompletionProductMap` is the pair of the original
infinite and finite adelic projections.
`numberFieldProductSubspaceAdeleTopology` is the induced full-product topology on
the original full number-field adelic carrier. Injectivity is proved using
extensionality of the infinite product and the finite restricted product.

The definitions have arbitrary common universe and preserve the original rings
and the independently supplied local coefficient topologies. The curve
construction does not require finite constants or a rational-function
presentation. These named topologies do not redefine the existing arithmetic
adelic topology. This unit does not prove their comparison with any projective
subspace topology, their non-local-compactness, or any rational-point density
assertion. Those are separate obligations.
