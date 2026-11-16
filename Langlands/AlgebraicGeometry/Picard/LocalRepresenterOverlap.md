# The overlap scheme of a local presheaf representer

This is an internal construction from a supplied representation after base
restriction. It uses independent scheme and presheaf value universes, and no
sheaf condition.

For a local representer `M` over `U` and `p : U → S`, the overlap scheme is
`M ×_S U`. Its first map to `M` is the pullback projection. Its second map is
the unique local classifier of the first universal family restricted to this
scheme, using the second coordinate as its map to `U`.

`family_eq` verifies that both chart projections classify the same family.
`lift` and its projection lemmas express the universal property: a map to the
first chart with a chosen second covering-base coordinate has a unique
classifier as second projection. This is the initial part of the overlap
relation construction; no effective descent is asserted.
