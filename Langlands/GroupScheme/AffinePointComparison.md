# Reconstruction from actual affine group-valued points

This internal construction applies to two affine actual group schemes over the spectrum of any commutative ring in universe `u`. It reconstructs actual homomorphisms and isomorphisms from natural transformations and natural isomorphisms of their original group-valued affine-point functors. No commutativity, finite type, smoothness or field hypothesis is used.

The provenance is the published `AffineCorepresentation` and `Corepresented.groupSchemeMap` constructions, together with the canonical relative affine presentation `affineSchemeOverIso`. No external structural theorem is added. The imported modules document their own provenance.

`presentation` is the canonical spectrum presentation of the original affine scheme. `modelIso` recovers the actual group laws using the published instance `AffineCorepresentation.isMonHom_iso` and Mathlib's group-object isomorphism constructor. The reconstructed `map` first passes to the corepresented model, applies `Corepresented.groupSchemeMap` to the given transformation, and returns to the original target. The theorem `map_points` follows from that published map's point formula and the inverse laws of the affine presentation.

`hom_ext` tests equality on the canonical presentation point, which is an isomorphism onto the affine source. Applying this criterion to the two composites and using the inverse laws of a natural isomorphism proves that `iso` is an actual bundled group-scheme isomorphism. `iso_hom_points` records exactly the original affine-point transformation; thus reconstruction introduces no change of point coordinates.
