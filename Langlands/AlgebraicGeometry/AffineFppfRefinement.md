# Affine refinements of single fppf covers

`AffineFppfRefinement U` records one affine scheme `V` over a base `S`,
a morphism `V → U` over `S`, and flatness, surjectivity, and local finite
presentation of `V → S`. The comparison map `V → U` is not required to be
surjective. This distinction allows the original cover to have a total
space that is not quasi-compact.

For any quasi-compact scheme `S` and any flat, surjective, locally finitely
presented morphism `U → S`, `nonempty_affineFppfRefinement` constructs such
a refinement. It views `U → S` as a singleton cover. The morphism is open,
so Mathlib's quasi-compact-cover result produces a finite family of affine
charts refining it. The coproduct of this finite affine family is affine.
The induced map to `U` composes to the coproduct cover map to `S`.
Flatness and local finite presentation hold by locality at the source;
surjectivity follows because the family covers `S`.
`affineFppfRefinement` chooses the resulting data.

This is an internal construction using Mathlib's
`QuasiCompactCover.exists_hom`, finite affine coproducts and local morphism
properties. It imposes quasi-compactness on the base, with no
quasi-compactness condition on `U` or on its map to the base. It supplies
cover data only, without a group-scheme or cocycle assertion.
