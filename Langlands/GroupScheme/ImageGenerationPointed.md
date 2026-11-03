# Smooth connected generation from a pointed integral morphism

This module proves the published target
`Langlands.GroupScheme.PointedImageGenerationStatement.{u}` as
`Langlands.GroupScheme.ImageGeneration.pointedImageGeneration`, for an
arbitrary universe `u`.

Setting: `k` is an arbitrary field. `G` is an actual group scheme over
`Spec k` whose structure morphism is smooth and affine. `V` is an object over
`Spec k` whose structure morphism is affine, locally of finite type and
geometrically integral. `v₀` is a rational point of `V`, and `f : V ⟶ G.X` is a
morphism with `v₀ ≫ f = 1`. The theorem produces an actual
`D : GeneratedImage f` with `D.HasSmoothConnectedGeneration`.

The route follows Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, 2nd ed.
(2015), paragraph preceding Proposition 3.3.5 (printed p.109). The images of
the finite products stabilize, and a closed subsemigroup is a subgroup. The two
cited inputs (Borel 2.2 and EGA IV₄ 17.9.6) are not imported. They are replaced
by the internal arguments described below. Images are taken
scheme-theoretically, so no reducedness of the image is assumed. No
separability, perfectness or characteristic hypothesis is used.

## Helper modules

- `ImageGenerationFinitePower`: every finite power `finitePower V n` is affine,
  locally of finite type, geometrically reduced and geometrically irreducible
  (`FinitePowerGood`). Its underlying scheme is affine, locally Noetherian and
  integral.
- `ImageGenerationNoetherian`: an antitone sequence of prime ideals in a
  Noetherian ring stabilizes.
- `ImageGenerationSubgroup`: `closedSubgroup` and `closedSubgroupHom` turn a
  closed submonoid of `G` whose square is affine and locally Noetherian into an
  actual closed subgroup with the same underlying object.
- `ImageGenerationAppend`: concatenated, constant and padded points;
  schematic dominance of image factorizations and tensor squares; descent of
  geometric reducedness and irreducibility over `Spec k`.
- `ImageGenerationGeometry` (published): `GeneratedImage.ofGeometricPower`
  turns a geometrically reduced and irreducible closed subgroup with a dominant
  positive ordered product into a generated image with
  `HasSmoothConnectedGeneration`.

## Stabilization of the product kernels

`productKernel f n` is the kernel of the global-section map
`Γ(G, ⊤) → Γ(finitePower V n, ⊤)` of the ordered product `orderedPowerMap f n`.

- `productKernel_antitone`: the kernels decrease in `n`. By
  `padMap_orderedPowerMap`, padding with copies of `v₀` factors
  `orderedPowerMap f n` through `orderedPowerMap f (n + d)`.
- `productKernel_isPrime`: each kernel is prime, because `finitePower V n` is
  integral, so its ring of global sections is a domain.
- `exists_productKernel_stable`: there is `N₀` with
  `productKernel f m = productKernel f N₀` for all `m ≥ N₀`. The ring
  `Γ(G, ⊤)` is Noetherian, because `G` is affine and of finite type over `k`.
  The prime-chain stabilization lemma then applies.
- `ker_le_ker_of_productKernel_eq`: since `G` is affine, Mathlib's
  `Scheme.ker_of_isAffine` describes the ideal-sheaf kernel of each product map
  by its global kernel. So equal product kernels give comparable ideal-sheaf
  kernels.

## The product image

For each `n`, `productImage f n` is the scheme-theoretic image of
`(orderedPowerMap f n).left`, as an object over `Spec k`.
`productImageι f n : productImage f n ⟶ G.X` is its closed immersion, and
`productToImage f n : finitePower V n ⟶ productImage f n` is the factorization,
so `productToImage_comp` holds:
`productToImage f n ≫ productImageι f n = orderedPowerMap f n`.

- `ker_productImageι`: the kernel of the closed immersion is the kernel of the
  product map (Mathlib's `IdealSheafData.ker_subschemeι`).
- `isSchemeTheoreticallyDominant_productToImage`: the factorization is
  schematically dominant, since its target is affine. It is also dominant and
  quasi-compact, by Mathlib's instances for `toImage`.
- `finitePowerGood_productImage`: the product image is again affine, locally of
  finite type, geometrically reduced and geometrically irreducible. The first
  two properties hold because it is closed in the affine finite-type `G`. The
  geometric properties descend from `finitePower V n` along the quasi-compact
  schematically dominant factorization (`ImageGenerationAppend`).
- `exists_mul_productImage`: if the kernel of the `n`-th product is contained
  in that of the `(n + n)`-th product, the product image is closed under
  multiplication. There is then `m : Z ⊗ Z ⟶ Z`, for `Z = productImage f n`,
  with `m ≫ ι = (fst ≫ ι) * (snd ≫ ι)`. The kernel containment factors
  `orderedPowerMap f (n + n)` through `ι` (`exists_over_factor_of_ker_le`). On
  the square of `finitePower V n`, the concatenation of the two factors has
  ordered product `(fst ≫ orderedPowerMap f n) * (snd ≫ orderedPowerMap f n)`,
  by `appendPoint_orderedPowerMap`.
  This shows that the ambient product `(fst ≫ ι) * (snd ≫ ι)`, precomposed with
  `productToImage ⊗ₘ productToImage`, factors through `ι`. That tensor square
  is schematically dominant, since every structure morphism to `Spec k` is
  flat.
  Published `exists_over_factor_of_schematic_precomp` then factors the ambient
  product itself through `ι`.

## Assembly

`exists_generation_of_closedSubmonoid` takes a closed immersion `j : Z ⟶ G.X`
with a multiplication lift `m`, a unit lift `e`, and an affine, locally
Noetherian square `Z ⊗ Z`. It also needs `Z` geometrically reduced and
irreducible, a lift `g : V ⟶ Z` of `f`, and a positive `n` with a dominant
`t : finitePower V n ⟶ Z` such that `t ≫ j = orderedPowerMap f n`. It forms
`closedSubgroup j m hm e he` with inclusion `closedSubgroupHom`. The ordered
product of `g` in this subgroup equals `t`, by `orderedPowerMap_comp` and
because `j` is a monomorphism. `GeneratedImage.ofGeometricPower` then gives the
result.

`pointedImageGeneration` applies this with `N = 1 + N₀` and
`Z = productImage f N`:

- the kernels of the `N`-th and `(N + N)`-th products agree, since both indices
  are at least `N₀`, so `exists_mul_productImage` gives `m`;
- `Z` is good (`finitePowerGood_productImage`), and `Z ⊗ Z` is good by
  `finitePowerGood_tensor`, so it is affine and locally Noetherian;
- the unit lift is `constPoint v₀ N ≫ productToImage f N`, whose product is `1`;
- the lift of `f` is `g = appendPoint (singlePoint V) (constant v₀-tuple of
  length N₀) ≫ productToImage f N`. Its composite with `ι` is
  `f * 1 = f`, by `appendPoint_orderedPowerMap`, `singlePoint_orderedPowerMap`
  and `constPoint_orderedPowerMap`;
- `t = productToImage f N` is dominant and `N > 0`.

By `ofGeometricPower`, the resulting `GeneratedImage f` realizes the fixed
`closedImageEnvelope f`. Its group is smooth, affine and geometrically
connected, and its `N`-th power map is dominant.

The local field-spectrum instance is the existing attributed FLT instance
imported through `ImageGenerationFinitePower`.
