# Galois subgroup coordinates and integral corestriction

This derived supporting unit identifies the published integral Tate
corestriction in degree minus two with scalar restriction on the actual Galois
abelianizations. It does not prove the norm-subgroup existence theorem.

The field section uses a common arbitrary universe `u` and a tower `M/L/K`.
`relativeAbelianizationInclusion` is induced by the actual homomorphism
`Gal(M/L) → Gal(M/K)`. If `L/K` is normal, the image of this homomorphism is
the kernel of restriction to `Gal(L/K)`, so it is normal. If `M/K` is normal
as well, `relativeGaloisCosetEquiv` identifies the quotient by this image
with `Gal(L/K)`. The quotient equivalence itself needs no finiteness hypothesis.

The degree-minus-two comparison follows single first-homology chains through
group-coordinate change and subgroup corestriction. The resulting chain is
labelled by the same automorphism after restricting its scalar field. The
integral first-homology comparison identifies this chain with the corresponding
class in the actual Galois abelianization. Surjectivity of the single-chain
presentation extends the identity to every Tate class.

`integralSubgroupTateIso_minusTwoClass` proves the single-chain coordinate
identity, and `integralTateMinusTwoEquiv_corestriction` proves the resulting
identity on all integral Tate classes. These two results assume finite
dimensionality of `M/K` and `M/L`, without normality or a local-field premise.

The content is derived directly from the Library definitions of relative
Galois subgroups, Tate reindexing and subgroup corestriction, the Library
single-chain comparison for integral first homology, and Mathlib's normal
restriction and quotient-group theorems. It makes no new literature assertion
and imposes no normalization on a chosen norm equivalence.
