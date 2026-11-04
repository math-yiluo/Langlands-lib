# Actual normalizer points under the adjoint split-torus image

This internal construction starts with the actual quotient square supplied by
`IsAdjointSplitTorusImage q i j p`. It restricts the actual map on base points
induced by `q` to a group homomorphism `normalizerPoints i →* normalizerPoints j`.
Its value is the original point composed with `q`; no pointwise surjectivity
of `p` or `q` is assumed.

To construct the restriction, pull back the fppf torus map `p` over an arbitrary
test point of the target torus. Source normalizer conjugation and the original
quotient square show on this cover that conjugation by `q(n)` belongs to the
range of `j`. Effective-epimorphism descent through the monomorphism `j`
descends this membership. Represented-subgroup factorization constructs a
torus endomorphism. Repeating the construction for `n⁻¹` proves it is an
automorphism, by cancellation through `j`. The resulting normalizer map is
multiplicative because it is the restriction of the actual ambient point map.

`normalizingAut_comp` records the actual commuting square between `p` and the
source and target normalizer automorphisms. It follows by composing with `j`,
using the two normalizer identities and naturality of inner conjugation, and
cancelling the monomorphism.

This construction and its intrinsic identities are derived entirely from
the published `IsAdjointSplitTorusImage`, `IsNormalizingPoint`, `factorHom`,
and `mem_range_of_comp_mem_range` interfaces. No independent literature
assertion is formalized in this unit. It is internal infrastructure for the
KP program's comparison of real cocharacter actions. It does not construct
a building, an apartment map, or full cross-torus A2, and does not assert
surjectivity on normalizer rational points.
