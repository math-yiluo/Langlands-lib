# Represented products of a smooth connected subgroup with a normal one

This module proves
`Langlands.GroupScheme.SmoothConnectedNormalFactorFppfProductExistenceStatement`
(stated in `Langlands.GroupScheme.SubgroupFunctor.SmoothConnectedNormalFactorProductExistenceStatement`):
over an arbitrary field `k`, let `G` be an affine group scheme locally of finite type over
`Spec k`, and let `i : H ⟶ G`, `j : N ⟶ G` be closed subgroups with `H` and `N` smooth and
connected and the image of `j` normal. Then some smooth connected group scheme `P` with a
homomorphism `p : P ⟶ G` represents the fppf-local product of `range i` and `range j`, in
this order.

This is the smooth connected case of J. S. Milne, *Algebraic Groups* (2017), Theorem 5.82
(printed pp.120–121), where the product `H·N` is the image of the multiplication map
`N ⋊ H → G`; that `HN` is again smooth and connected is Milne's Lemma 6.41 (printed
p.134). The Lean proof constructs the product as that image, using Library results on
semidirect products and on images of homomorphisms; smoothness and connectedness come
from the image theorem applied to the smooth connected scheme `N ⋊ H` rather than from
Lemma 6.41's quotient argument.

## Swapping the order of a local product

- `SubgroupFunctor.FppfLocallyInProduct.swap_of_isNormal_left`: if `N` is normal and a point
  `x` of `G` is, fppf-locally, a product `n * f` with `n ∈ N` and `f ∈ F`, then it is also
  fppf-locally a product `f * (f⁻¹ * n * f)` with the second factor in `N`.
- `SubgroupFunctor.FppfLocallyInProduct.swap_of_isNormal_right`: conversely, `f * n` equals
  `(f * n * f⁻¹) * f`, so a local product in the order `F, N` is one in the order `N, F`.
  Both proofs use the same fppf cover as the input.
- `SubgroupFunctor.IsFppfProduct.swap`: a closed subgroup representing the local product of
  `N` and `F` with `N` normal also represents the local product of `F` and `N`; the closed
  subgroup condition is unchanged and the membership equivalence is composed with the two
  swap lemmas.

## The product as an image

`SmoothConnectedNormalFactorProduct.exists_isFppfProduct` constructs `P`:

1. Normality of `range j` gives that `range i` normalizes `range j`. The Library's
   `AutomorphicAction.ofNormalizedConjugation j i` is the conjugation action of `H` on `N`,
   and `SubgroupFunctor.normalizedProductHom j i` is the homomorphism
   `φ : N ⋊ H ⟶ G`, `(n, h) ↦ j(n) * i(h)`, on the semidirect product, whose underlying
   scheme is `N.X ⊗ H.X`.
2. `smoothConnectedAffineGeometry` shows that `N.X ⊗ H.X` is affine and geometrically
   integral over `k`; hence it is irreducible (a geometrically irreducible scheme over a
   one-point base) and connected. It is smooth as a composite of base changes of smooth
   morphisms.
3. `smoothConnectedHomImage` applied to `φ` gives a closed subgroup `inc : D ⟶ G` and a
   factorization `φ = fac ≫ inc` whose underlying morphism `q` is flat, surjective and
   locally of finite presentation, with `D` smooth and connected.
4. `q ≫ inc` is the pointwise product of the two projections composed with `j` and `i`
   (`SubgroupFunctor.normalizedProductHom_hom`). By
   `SubgroupFunctor.isFppfProduct_of_fppf_factorization`, `inc` represents the local
   product of `range j` and `range i`; `IsFppfProduct.swap` with the normality of
   `range j` turns this into the product of `range i` and `range j`.

The theorem `smoothConnectedNormalFactorFppfProductExistence` introduces the quantified
data of the proposition and applies `exists_isFppfProduct`.
