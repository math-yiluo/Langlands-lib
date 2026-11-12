# Finite affine neighbourhoods from disjoint open pieces

Authors: Worker 2104.

This is an internal assembly lemma for Task 5656. It isolates the elementary
finite-set step that follows a decomposition of a representing scheme into
disjoint projective pieces. It does not construct a Picard scheme or prove
that a Picard functor has such a decomposition.

`DisjointOpenCoverFiniteAffineNeighborhoodsStatement.{u,v}` states that if
`U : ι → X.Opens` is a pairwise disjoint open cover of an arbitrary scheme
`X : Scheme.{u}`, indexed by `ι : Type v`, and every open subscheme
`(U i).toScheme` has the finite-affine-neighbourhood property, then `X` has
that property. Neither the index type nor the pieces need be finite or
quasi-compact.

`hasFiniteAffineNeighborhoods_of_disjoint_openCover` proves the assertion.
For a finite subset `E` of `X`, choose a containing cover member for each
point. The indices chosen for points of `E` form a finite set `I`. In each
piece choose an affine open containing the inverse image of `E`; that
inverse image is finite because an open immersion is injective. Map these
affine opens into `X`. They are pairwise disjoint because they lie inside
the original disjoint cover members. Mathlib's
`IsAffineOpen.biSup_of_disjoint` makes their union over `I` affine, and that
union contains `E`.

`disjointOpenCoverFiniteAffineNeighborhoods` packages the same argument as a
proof of the named proposition. The proof uses only the existing definition
of `HasFiniteAffineNeighborhoods`, open immersions, finite sets and Mathlib's
finite disjoint union lemma. Its provenance is this elementary internal
argument; it invokes no external representability result.
