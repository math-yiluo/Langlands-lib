# Creation and multiplication-slant contraction on actual cohomology

This internal construction specializes the existing ordered Čech creation and shuffle slant
maps to an abelian scheme `A` over a field `K`. All cohomology objects are
`structureCohomology X n = (relativeCohomology X.hom n).obj 𝒪_X`.

`creation A n` is `AllSeq.creationCanonical` on the fixed finite affine cover `cover A`.
It is linear in its degree-one creating class and in its degree-`n` argument.
`creation_one` identifies its degree-one component with `cupA A`.

`slant A ell n` is `AllSeq.slantByH1Dual` on the simple product cover `mixedCover A`.
Its functional comes from the actual dual `ell : H¹(A) →ₗ[K] K` by the fixed cocycle
retraction in `AllSeqSlantDual`. Its codomain is `Hⁿ(A)` and its domain is `Hⁿ⁺¹(A × A)`.
`contraction A ell n` first applies the canonical multiplication pullback
`m* : Hⁿ⁺¹(A) → Hⁿ⁺¹(A × A)` and then this slant.
Here `m = prod.fst * prod.snd` in `Over (Spec K)`.

In degree two, `slant_pull_left` and `slant_pull_right` kill the two projection
pullbacks, by `AllSeqAxisSlant`. `slant_mixed_cup` sends
`p₁* x ∪ p₂* y` to `ell x • y`. The comparison `cupP_eq_mixedCover` identifies the
cup on the multiplication-adapted cover with the cup on the simple product cover,
so this formula uses the same product as `pullStructure_mul_cupA`.
Applying these three identities to that multiplication formula gives

`contraction A ell 1 (cupA A x y) = ell x • y - ell y • x`.

This formula describes contraction only on cups of degree-one classes. The module
does not assert that such cups span degree two. General creation-contraction
relations, bottom-degree formulas, a cohomological degree bound, alternation in
characteristic two and the exterior/coproduct comparison remain separate obligations.
No excluded Picard or dual-geometry result is used.

The provenance is entirely internal: the definitions specialize
`AllSeqCreation` and `AllSeqSlantDual`, and the displayed formula combines
`pullStructure_mul_cupA` from `CanonicalH1Primitive`, `AllSeqAxisSlant`, `AllSeqMixedSlant` and the refinement comparison in
`DegreeTwoComparisonAssembly`. No new external literature theorem is asserted.
