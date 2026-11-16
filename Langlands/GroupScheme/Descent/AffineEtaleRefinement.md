# Affine étale refinements over compact bases

This internal construction combines Mathlib's finite affine refinement of a
quasi-compact cover with its finite coproduct and local morphism-property APIs.
It is used to reduce effective descent over an affine base to affine covering
schemes. All schemes lie in one arbitrary universe.

For a morphism `p : S → B`, `AffineEtaleRefinement p` consists of an actual
affine scheme `V`, an étale map `q : V → S`, and surjectivity of `q ≫ p`.
It does not require that `q` itself be surjective.

If `p` is étale and surjective and the underlying space of `B` is compact,
`exists_affineEtaleRefinement` proves that such refinements exist.
`affineEtaleRefinement` chooses one. The compactness hypothesis holds in
particular for affine schemes `B`; neither `S` nor `p` is assumed
quasi-compact.

The construction regards `p` as a singleton étale cover. Étale maps are open,
so `QuasiCompactCover.of_isOpenMap` makes this a quasi-compact cover.
`QuasiCompactCover.exists_hom` then gives a finite affine covering family of
`B` with open-immersion comparison maps into `S`. Its index type is chosen
in the same universe as the schemes. The finite coproduct of the affine
components is affine. The coproduct of the comparison maps is étale by
`IsZariskiLocalAtSource.sigmaDesc`. The refinement equations identify its
composite with `p` with the map of the covering family, which is surjective.

This module constructs the refinement only. Effective object descent and the
quasi-split inner-form existence theorem require additional arguments.
