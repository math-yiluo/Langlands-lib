# Left translation of covariant coordinates by a rational point

Worker 1330 derives this internal support from the published evaluation of
affine coordinates on test schemes and the published inner automorphisms. It
shows that conjugating a subgroup map by a rational point does not change its
covariant coordinate spaces up to isomorphism. The intended use is a Borel
subgroup `B` and its opposite `B⁻ = n B n⁻¹`, for a representative `n` of the
longest Weyl element. Their section modules then have equal dimensions, as
required for tensor products whose two factors share one coordinate type. That
application, including any Borel subgroup or Weyl element, is not part of this
file.

## Setting

Let `k` be a field and `G` an actual group scheme over `Spec k` with affine
total space. A rational point is a morphism
`n : Over.mk (𝟙 (Spec k)) ⟶ G.X`. The published `G.constantPoint n T` pulls it
back to every test scheme `T`, and `G.innerIso n` is the published inner
automorphism, which acts by `x ↦ n x n⁻¹` on test points.

## Left translation

`leftTranslate G n` is the algebra map on the coordinate algebra given by
`(L_n f)(g) = f(n g)`. It evaluates the coordinates at the actual test point
`constantPoint n G.X * 𝟙` on the total space of `G`. It then identifies the
resulting global function with a coordinate through the inverse of the
published `globalAlgEquiv`.

- `pointAlgebraHom_leftTranslate`: for every test scheme `T`, every
  `g ∈ G(T)` and every coordinate `f`, the value of `L_n f` at `g` is the value
  of `f` at `constantPoint n T * g`. The proof uses the published
  `pointAlgebraHom_apply_eq` and `pointAlgebraHom_naturality`. Precomposition
  with `g` distributes over the product of points (`MonObj.comp_mul`), and
  `constantPoint_naturality` handles the pulled-back point.
- `ext_pointAlgebraHom`: two coordinates with equal values at all test points
  are equal. Indeed, evaluation at the identity point is the bijection
  `globalAlgHom`.
- `leftTranslate_inv_leftTranslate` and `leftTranslate_leftTranslate_inv`:
  `L_(n⁻¹)` and `L_n` are mutually inverse. Pointwise this is
  `n⁻¹ (n g) = g` and `n (n⁻¹ g) = g`, using the published `constantPoint_inv`.

## Covariant coordinates of a conjugate

Now let `G` and `H` have affine structure morphisms, `i : H ⟶ G` be an actual
homomorphism, and `χ` be a coordinate of `H`. The `n`-conjugate of `i` is
`i ≫ (G.innerIso n).hom`. `comp_conj_hom` states that on a test point `h` of
`H` it is `n_T (h ≫ i) n_T⁻¹`, where `n_T = constantPoint n T`.

The covariant subspaces are the published `leftCovariantSubspace`.
Covariance is checked on test points through the published
`mem_leftCovariantSubspace_iff_points`.

- `leftTranslate_mem_leftCovariantSubspace`: if `f` is covariant of weight `χ`
  for the `n`-conjugate of `i`, then `L_n f` is covariant of weight `χ` for `i`.
  Indeed, `(L_n f)(i(h) g) = f(n i(h) g) = f((n i(h) n⁻¹)(n g)) = χ(h) (L_n f)(g)`.
- `leftTranslate_inv_mem_leftCovariantSubspace`: conversely, if `f` is covariant
  for `i`, then `L_(n⁻¹) f` is covariant of the same weight for the
  `n`-conjugate of `i`. Indeed, `f(n⁻¹ (n i(h) n⁻¹) g) = f(i(h) n⁻¹ g)`.

In both proofs the group identity between the test points is closed by the
`group` tactic.

- `leftCovariantConjEquiv i n χ` is the resulting `k`-linear equivalence
  between the covariant subspaces of `i` and of its `n`-conjugate, for the same
  weight `χ`. It sends `f` to `L_(n⁻¹) f`, with inverse `L_n`.
- `leftCovariantConjBasis` transports a basis of the first space along this
  equivalence to a basis of the second, indexed by the same type.

## Scope

The file proves only this transport. It does not show that any particular
subgroup is conjugate to another, and it does not compare right-translation
representations beyond the existence of the linear equivalence.
