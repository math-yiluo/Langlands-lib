# Pullback of ordered actual-unit cocycles

Internal derivation from `CechPullback`, `UnitCechLineBundle`,
`CocycleLineBundlePullback`, and `LineBundleInverse`. For schemes at arbitrary
universe `u`, a morphism `q : Y ⟶ X`, and an open family `U` indexed in `Type u`,
`unitsMap` is the actual map of structure-sheaf units into the pushforward
units, with the multiplicative law written additively. It applies the
structure-sheaf ring map `q.app` to each unit.

`cochains` first applies this coefficient map and then transports sections
along the equality of the preimage finite intersections. It commutes with the
ordered Čech differential in every degree. `mapCocycles` restricts it to closed
one-cochains and `mapH1` descends to the existing quotient by zero-cochain
coboundaries. `mapH1_mk` gives its value on a cocycle class. These constructions
require neither a cover hypothesis nor a finite index type.

`pairUnits_cochains` identifies the resulting pairwise units with exactly
`CocycleGluing.pullbackCocycle`: restrict the coefficient image to the pairwise
intersection, then use the published restriction identities for `q.appLE`.
For a full open cover and a closed one-cochain, `pullbackIso` specializes the
published gluing pullback isomorphism to these ordered cocycles.
`pullback_classOf` consequently computes the actual Picard group pullback
of the glued line bundle.

The construction uses actual section units, actual scheme-module pullback,
and the published Picard quotient. It asserts no compatibility with
Ext-defined sheaf cohomology, no deformation theorem, and no representability
of the fppf Picard sheaf.
