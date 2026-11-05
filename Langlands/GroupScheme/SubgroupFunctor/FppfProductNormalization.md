# Normalization through represented fppf products

Author: Worker 60.

These internal subgroup-functor lemmas work over an arbitrary base scheme
`S : Scheme.{u}` and retain all relative tests.

`IsFppfProduct.normalizes` says that an fppf-local subgroup functor `A`
normalized by each of `F` and `N` is normalized by the image of any actual
representative `i : P → G` of their fppf-local product. For `g` in that
image, choose its fppf-local factorization `g = p n`. Restrict a point `x`
of `A` to that cover. First conjugate by `n`, then by `p`; membership of
`g x g⁻¹` descends by the supplied fppf-locality of `A`. No lift or
factorization on the original test is assumed.

`IsFppfProduct.isNormalizedBy` says that if `F` and `N` are normalized by
`A`, then their represented product is normalized by `A`. Factor the
point being conjugated after a cover, conjugate both factors there, and
descend membership in the represented product using its existing
`isFppfLocal` theorem.

`isNormalizedBy_of_le` is the pointwise subgroup fact that `N` is normalized
by every subgroup `F ≤ N`. `isNormal_range_of_isNormalizedBy_comp` says
that, for `q : D → P` and monic `i : P → G`, relative normalization of
`range (q ≫ i)` by `range i` gives normality of `range q` in `P`.
Map a conjugate into `G`, obtain a point of `D` from relative
normalization, and cancel the monomorphism `i`.

The provenance is internal group algebra and fppf membership descent,
extending the Library's existing product-normality and monic-reflection
lemmas. The motivating application is the normality step in the first
paragraph of the proof of Conrad–Gabber–Prasad, *Pseudo-reductive groups*,
second edition (2015), Corollary 2.2.5, printed p.64 (one-based PDF p.90).
That step uses `P = P_G(λ) R_us,k(G)` to show that
`U_G(λ) R_us,k(G)` is normal in `P`. The source is registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The lemmas here assert no product or radical existence and do not prove
the product replacement of Proposition 2.2.4.
