# Affine pinned models preserving a supplied maximal torus

This is an internal packaging of the Library's
`exists_etale_affine_splitCoordinates_of_suppliedTorus` and root-base
existence theorem. It introduces no external-source theorem.

`SuppliedTorusAffineChart` retains an affine pinned model, its etale map to
the original base, actual group and commutative-torus isomorphisms to the
direct pullbacks of the supplied groups, and their exact inclusion square.
`SuppliedTorusAffineChart.exists_over` constructs such a chart over every
point of an arbitrary base from a reductive ambient group, a supplied
relative torus and its closed fibrewise maximal inclusion. No torus is
chosen independently of the supplied one.

The proof uses the published local coordinate theorem for that same torus.
Its actual coordinate isomorphism, inclusion, full realized root datum and
free actual root-weight lines supply the corresponding fields of the affine
model. A root base is chosen for this datum; the free lines supply its
pinning. The model's ambient group is the direct pullback of the original
group, so its ambient comparison is the identity. The coordinate group
isomorphism lifts to a commutative-group isomorphism, and the inclusion
square follows from the definition of the coordinate inclusion.

The construction requires neither a Borel nor a Borel-adapted initial
pinning. It does not yet construct the supplied-Borel permutation atlas or
prove the final Weil presentation.
