# Actual products of base changes along embeddings, on homomorphisms

This internal unit supplies the product side of the embedding splitting of affine Weil
restriction. It only uses the categorical finite product `GroupScheme.pi`, the actual
base-change functor `GroupScheme.baseChange` and Mathlib's `Limits.Pi.map`; no group is
assumed commutative, smooth or of any special shape.

## Generic finite products

For a finite family of homomorphisms `f i : G i ⟶ G' i` of group schemes over a scheme `S`,
`Limits.Pi.map f : pi G ⟶ pi G'` is the actual product homomorphism.

- `pi_map_hom_π`: its composite with the `i`-th projection, on underlying morphisms over `S`,
  is the `i`-th projection followed by `f i`. This is `Limits.Pi.map_π` read on underlying
  morphisms.
- `piPointsEquiv_pi_map`, `piPointsEquiv_symm_pi_map`: under the published
  `piPointsEquiv`, the product homomorphism applies `f i` to the `i`-th coordinate of a point
  over any test object `T`, and reassembling a family of points commutes with it.
- `piPointsEquiv_affinePointsTarget_pi_map`: the same formula on points with coefficients in
  an algebra `A` over the base ring, written with `affinePointsTarget`.

## The embedding product

Let `k`, `K`, `Ω` be commutative rings in one universe, with `k`-algebra structures on `K`
and `Ω`, and assume the set of `k`-algebra maps `K →ₐ[k] Ω` is finite (for fields with `K`
finite-dimensional over `k` this is a Mathlib instance). For a group scheme `H` over
`Spec K`, the embedding product is

`GroupScheme.pi (fun τ : K →ₐ[k] Ω => (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj H)`,

written out explicitly in every statement.

- `baseChange_spec_isAffine`: the base change of a group scheme with affine underlying scheme
  along any map `Spec D ⟶ Spec C` has affine underlying scheme, since it is the pullback of
  affine schemes.
- `embeddingProduct_isAffine`: if `H.X.left` is affine, so is the underlying scheme of the
  embedding product. Each factor's structure morphism is affine, so the published
  `prop_pi_hom` shows the product's structure morphism is affine, and its target is affine.
- `embeddingProductMap k f`, for `f : H ⟶ H'`, is `Limits.Pi.map` of the base changes of `f`
  along all `τ`.
- `embeddingProductMap_π`, `embeddingProductMap_hom_π`: its `τ`-projection is the
  `τ`-projection followed by the base change of `f` along `τ`, as group-scheme homomorphisms
  and on underlying morphisms.
- `embeddingProductMap_id`, `embeddingProductMap_comp`: it preserves identities and
  composition. Both are proved by the universal property of the product (`Limits.Pi.hom_ext`)
  from the projection formula and the functoriality of base change.
- `piPointsEquiv_embeddingProductMap`, `piPointsEquiv_affinePointsTarget_embeddingProductMap`:
  on points over any test object, and on points with coefficients in an `Ω`-algebra `R`, the
  `τ`-coordinate of the image of a point is the image of its `τ`-coordinate under the base
  change of `f` along `τ`.

These are the product-side facts needed to state and prove the naturality of the embedding
splitting under homomorphisms `H ⟶ H'`.
