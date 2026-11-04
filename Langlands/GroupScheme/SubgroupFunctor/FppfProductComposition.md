# Composing fppf-local subgroup factorizations

This module defines
`SubgroupFunctor.FppfLocallyContainedInProduct A F N`: every point of the
subgroup functor `A`, on every relative scheme test, belongs to the existing
fppf-local ordered product of `F` and `N`. This is an internal interface
derived directly from `SubgroupFunctor.FppfLocallyInProduct`, with no
additional geometric theorem or external source.

The definition quantifies over every `T : Over S` and `x : T ⟶ G.X`.
It assumes membership in `A.carrier T` and requires
`FppfLocallyInProduct F N x`. It retains the flat, surjective, locally
finitely presented cover and the order of factors in that existing predicate.
The base scheme `S` and the group scheme `G` are arbitrary. No affineness,
normality, representability, field, or reducedness assumption is made.

The implemented lemmas combine local factorizations:

- `FppfLocallyInProduct.of_comp` composes a supplied fppf cover with the cover
  witnessing a factorization after it. Flatness, surjectivity, and local
  finite presentation are preserved by composition.
- `mul_left` pulls a point of `F` to the witnessing cover and multiplies it
  into the left factor. Subgroup closure and associativity give the result.
- `replace_right` starts with a local factorization `x = p * n`, factors
  `n` locally into `F * N'`, and applies the preceding lemmas. The result
  is a factorization into `F * N'` after the composite cover.
- In the definition's namespace, `of_le` obtains local containment from
  actual subgroup containment, `replace_right` applies the same substitution
  to every point of another subgroup, and `product_iff` combines substitution
  with monotonicity when `N' ≤ N`.

These proofs apply to nonaffine and nonreduced tests. They require no local
factorization on the original test and construct no representative of a
product. Their intended use is to reduce a product equality to local
containment of its right factor. They do not establish the structural
containment of an ordinary unipotent radical in a dynamic parabolic times
the split radical.
