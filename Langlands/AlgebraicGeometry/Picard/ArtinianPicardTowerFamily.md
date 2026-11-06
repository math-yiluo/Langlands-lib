# Actual line-bundle transitions on the Picard source tower

This is an internal construction from `ArtinianPicardSourceStep`,
`ArtinianPicardSourceTower` and `ArtinianPicardTowerMaps`. Fix a commutative
base ring k, a residue field K with a k-algebra structure, a noetherian local
k-algebra R with a surjective k-augmentation to K, a proper flat scheme over
k, an actual residue-fibre line bundle M, and an initial `Stage` of the
published source construction. No residue coefficient section is assumed.
All rings and schemes retain the displayed arbitrary universe.

`bundleStep` extracts the underlying actual line-bundle isomorphism from the
published pointed successor transition. Its source is ordinary pullback along
the exact relative scheme map of `Stage.reduction`; its target is the old
underlying bundle. `bundle` is the underlying actual line bundle of the
published pointed family at each tower stage.

For every n at most m, `hasTransition` proves that ordinary pullback of the
stage-m bundle along the exact published `towerMap` is isomorphic to the
stage-n bundle. The proof inducts on the later stage. At equality it uses
the identity equation for `towerMap`, functoriality of the actual relative
scheme map, and the line-bundle pullback identity comparison. At a successor,
the tower-map composition equation identifies the actual relative map with
the composite through stage m. Equality transport and the inverse ordinary
pullback-composition comparison reduce to two successive pullbacks. Pulling
back `bundleStep` and composing with the inductive isomorphism proves the
claim.

`transitionIso` chooses an actual line-bundle isomorphism from that proved
nonemptiness. No identity or composition law is asserted for these choices,
and no compatibility equation with the pointed residue identifications is
asserted here. The original tower families remain pointed objects; this
module supplies their underlying bundle transitions for the formal-system
construction. It uses neither completeness nor cofinality and does not
assert a formal family over adic quotients, formal versality or an atlas.
