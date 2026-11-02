# Conjugation on a normalized subgroup as a morphism of schemes

Let `iH : H ⟶ G` and `iK : K ⟶ G` be homomorphisms of group schemes over an arbitrary
scheme `S`. Suppose the published subgroup functor `range iH` is normalized by
`range iK`, in the published sense of `SubgroupFunctor.IsNormalizedBy`: conjugation
preserves membership on every test scheme over `S`.

This internal construction turns that condition into an actual morphism
`K ×_S H ⟶ H`. If `iH` is a monomorphism of schemes over `S`, the morphism is unique
and gives an action by group automorphisms, naturally on every test scheme.
No smoothness, reducedness, affineness, finite presentation, or separatedness
hypothesis is imposed on these group schemes or on the base.

## Provenance

This is a derived construction using the published `SubgroupFunctor.range` and
`IsNormalizedBy`, the group structures on groups of points, and products in
`Over S`. It adds no external structural theorem. Applying the all-test
normalization condition to the two universal projections gives the
factorization. Conversely, pulling that factorization back along a pair of
points proves the all-test condition. This is the elementary representable
functor interpretation of normalization.

## Morphisms and factorization

All declarations are in `Langlands.GroupScheme.SubgroupFunctor`.

- `conjugationMap iH iK : K.X ⊗ H.X ⟶ G.X` is
  `(pr₁ ≫ iK) * (pr₂ ≫ iH) * (pr₁ ≫ iK)⁻¹`, using the group structure on
  morphisms into `G`.
- `lift_comp_conjugationMap` computes its value on a pair of arbitrary test
  points as `(g ≫ iK) * (h ≫ iH) * (g ≫ iK)⁻¹`.
- `isNormalizedBy_range_iff_exists_conjugationMap` proves that normalization on
  all tests is equivalent to the existence of a morphism `a : K ×_S H ⟶ H`
  whose composite with `iH` is `conjugationMap iH iK`. This equivalence does not
  require `iH` to be a monomorphism.
- `normalizedConjugation iH iK hn` chooses such a factorization.
  `normalizedConjugation_comp` is its defining equation, and
  `lift_comp_normalizedConjugation_comp` gives its value after `iH` on every
  pair of test points.
- `normalizedConjugation_naturality` expresses restriction of these point maps
  along any morphism of test schemes. It follows directly from the product
  pairing and associativity of composition.

## Action by automorphisms

The following declarations require `Mono iH.hom.hom`, the monomorphism
condition on the underlying morphism in `Over S`.

- `normalizedConjugation_unique` proves uniqueness of the factorization by
  cancelling `iH`.
- `normalizedConjugation_one_left`, `normalizedConjugation_mul_left`, and
  `normalizedConjugation_mul_right` prove that the identity of `K` acts
  trivially, multiplication in `K` acts by composition, and each action map
  preserves multiplication in `H`. The proofs cancel `iH` and use the
  corresponding elementary conjugation identities in the group of
  `T`-points of `G`.
- `normalizedConjAut iH iK hn T g` is the resulting automorphism of `H(T)`.
  Its inverse is the action of `g⁻¹`; the action laws prove both inverse
  identities.
- `normalizedConjAction iH iK hn T : K(T) →* MulAut H(T)` bundles these
  automorphisms as a group homomorphism. The `_apply` lemmas identify both
  bundled maps with composition of the product pairing with the same
  morphism `normalizedConjugation`.

Thus the point actions are induced by a single morphism of schemes, rather
than assumed as additional data. The construction concerns normalization of
the images in `G`; it does not construct a representing normalizer subgroup
or a quotient by `H`.
