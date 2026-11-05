# Actual affine sections in infinitesimal squares

This internal prerequisite transports the published flat tensor preservation
of a categorical ring pullback through actual pushout identifications.
`tensorPushoutIso` identifies an arbitrary specified pushout of two algebra
structure maps with the ordinary algebra tensor product. Its left and right
formulas retain the two actual ring maps, and `tensorPushoutIso_naturality`
compares an actual morphism of such pushouts with the tensor of the prescribed
algebra map. `isPullback_of_pushouts` then transports all four vertices and
arrows of the flatly tensored ring square along these isomorphisms.

The construction is internal and follows from Mathlib's commutative-ring tensor
pushout universal property and the published `isPullback_tensor`. Flatness of
the tensor coefficient algebra and the eight map-compatibility equations are
explicit premises. No arbitrary base-change preservation is asserted.
