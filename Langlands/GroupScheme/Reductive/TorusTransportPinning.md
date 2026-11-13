# Pinnings transported through an aligned torus

This internal construction transports an actual root datum and its supplied
base through an isomorphism of tori. The character map is precomposition with
the inverse isomorphism; the contravariant coweight map is postcomposition with
the inverse. Their pairing identity proves that these maps form an equivalence
of root data. The root indices, simple-root support and Cartan pairings remain
unchanged. Reducedness follows by transporting linear dependence of two roots.

`GaloisPinningData.ofTorusIso` starts with a maximal torus defined over the ground
field and an isomorphism, over the separable closure, to the maximal torus of
a supplied split pinning. An ambient group isomorphism and a commuting square
identify their embeddings. The construction transports the supplied root datum
and base back to the descended torus. The actual-root-datum predicate is
preserved by the Library's torus transport theorem, and the published split
root-line theorem supplies Lie trivializations for this precise base.

The induced bijection of simple vertices keeps each original root index, and
every Cartan pairing is unchanged. If the scalar extension of a map from a
ground-field split torus, followed by the aligned torus isomorphism, equals a
prescribed map `ψ`, then the actual absolute-root restriction is the inverse
canonical character-base-change image of `ψ` followed by the original root
character. This identity follows by unfolding the transported root and
associating character pullback; it retains the prescribed map exactly.

The provenance is the Library's actual lattice transport, field extension,
maximal-torus scalar extension and root-line theorems, together with Mathlib's
base transport construction. No classification or type C restriction calculation
is asserted here.
