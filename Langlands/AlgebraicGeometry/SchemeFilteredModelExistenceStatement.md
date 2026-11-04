# Initial finitely presented scheme models over filtered ring colimits

`Langlands.AlgebraicGeometry.SchemeLimitModel.SchemeFilteredModelExistence`
states the first existence assertion of Conrad, *Weil and Grothendieck
approaches to adelic points* (2011), Theorem 3.4(1), printed p. 5.
The source is registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

For any small filtered category `J` and diagram `F` of commutative rings,
let `c` be an actual cocone and let `hc` certify that it is a colimit.
For an actual scheme morphism `g : X → Spec c.pt`, assume
quasi-compactness, quasi-separatedness and local finite presentation.
The conclusion gives a stage `j`, an actual scheme `Xj`, and a structural
morphism `gj : Xj → Spec (F.obj j)` with those same three properties.
It also gives a morphism `π : X → Xj` and a pullback square with
bottom map `Spec.map (c.ι.app j)`.

Thus `X`, together with its specified structural map, is isomorphic to the
base change of `Xj` along the actual ring-cocone map. The pullback condition
expresses that comparison without choosing an additional isomorphism.
The three finiteness conditions express the source's finite-presentation
convention, which includes quasi-compact affine overlaps. Neither `X`
nor `Xj` is required to be affine or separated.

The use of a small filtered category in place of a directed partially
ordered set is a derived categorical extension of the source formulation.
All ring carriers, the object and morphism types of the small category,
and schemes use an arbitrary universe `u`. Ring transitions need not be
injective; the cocone's apex need not be noetherian.

This file defines a proposition. The relative Hom comparison, prescribed
isomorphism descent, property descent in Theorem 3.4(2), and arithmetic
or topological specializations are separate assertions.
