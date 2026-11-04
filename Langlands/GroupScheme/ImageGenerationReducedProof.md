# Smooth generation by a geometrically reduced affine source

This module proves the published target
`Langlands.GroupScheme.GeometricallyReducedAffineImageGenerationStatement.{u}`
as `Langlands.GroupScheme.ImageGeneration.geometricallyReducedAffineImageGeneration`,
for an arbitrary universe `u`.

Setting: `k` is an arbitrary field. `G` is an actual group scheme over
`Spec k` whose structure morphism is affine and locally of finite type; `G` need
not be smooth. `V` is an object over `Spec k` whose structure morphism is
affine, locally of finite type and geometrically reduced. `V` may be empty or
disconnected, and no point of `V` is chosen. For every `f : V ⟶ G.X` the theorem
gives an actual `E : GeneratedImage f` with `Smooth E.group.X.hom`. The proof
uses no separability, perfectness or characteristic hypothesis.

The construction follows the affine case of Milne, *Algebraic Groups* (2017),
Propositions 2.46–2.48 (printed pp.54–55). The subgroup is cut out by the
intersection of the kernels of the coordinate-ring maps of the ordered products
`V^n → G`. There are three differences from Milne's text:

- the product with `n = 0` (the constant map to the identity) is included, so
  no point `o` with `φ(o) = e` is needed;
- inverses are not adjoined to the source. The intersection gives a closed
  submonoid, and a closed submonoid of an affine finite-type group over a field
  is a subgroup (`closedSubgroup` from `ImageGenerationSubgroup`);
- Milne's step "the intersection `I` of the `I_n` is stable under
  comultiplication" is proved with a tensor-product joint-injectivity lemma
  (`ImageGenerationJointInjective`), since the intersection is infinite and the
  chain of kernels need not be monotone without a point.

Smoothness then comes from Mathlib's theorem that a geometrically reduced group
scheme locally of finite type over a field is smooth.

## Helper modules

- `ImageGenerationJointInjective` (new, submitted with this proof): over a
  field, for affine schemes, if the global-section maps of the families
  `a i : X' i ⟶ X` and `b j : Y' j ⟶ Y` are each jointly injective, so are those
  of `a i ⊗ₘ b j` (`appTop_tensorHom_eq_zero`).
- `ImageGenerationPointed` (published): `productKernel f n`, the kernel of the
  global-section map `Γ(G, ⊤) → Γ(finitePower V n, ⊤)` of `orderedPowerMap f n`.
- `ImageGenerationProducts` and `ImageGenerationAppend` (published):
  `orderedPowerMap`, `orderedPowerMap_zero`, `orderedPowerMap_comp`,
  `appendPoint_orderedPowerMap`, `singlePoint_orderedPowerMap`, and
  `exists_over_factor_of_ker_le` (a morphism factors through a closed immersion
  when the kernel of the immersion lies in its kernel).
- `ImageGenerationSubgroup` (published): `closedSubgroup`, `closedSubgroupHom`
  and `isClosedSubgroup_closedSubgroupHom`. They make a closed submonoid whose
  square is affine and locally Noetherian into an actual closed subgroup with
  the same underlying object.

## Finite powers of the source

`ReducedPowerGood B X` says that `X.hom` is affine, locally of finite type and
geometrically reduced.

- `reducedPowerGood_of_iso` and `reducedPowerGood_tensor`: the property is
  invariant under isomorphism and stable under `⊗`. For `⊗`, the structure
  morphism of `X ⊗ Y` is `pullback.fst ≫ X.hom`. `pullback.fst` is affine
  (base change), and geometric reducedness is stable under composition and
  base change.
- `affineFiniteType_tensor`: the same for affine and locally of finite type
  alone.
- The terminal object `Over.mk (𝟙 _)` has the property, so it is closed under
  finite products (`ObjectProperty.IsClosedUnderFiniteProducts.mk'`).
  `reducedPowerGood_finitePower` then shows that every `finitePower V n` has it.
  In particular its underlying scheme is affine.

## The word closure

In section `WordClosure`, `G` has affine underlying scheme, and `f : V ⟶ G.X`.

- `wordKernel f := ⨅ n, productKernel f n`, an ideal of `Γ(G, ⊤)`. It runs over
  all `n`, including `n = 0`.
- `wordClosure f`: the closed subscheme of `G` cut out by
  `IdealSheafData.ofIdealTop (wordKernel f)`, as an object over `Spec k`.
  `wordClosureι f` is its closed immersion into `G.X`. It is affine.
- `ker_appTop_wordClosureι`: the kernel of the global-section map of
  `wordClosureι f` is exactly `wordKernel f`. This uses Mathlib's
  `ker_subschemeι_app` at the affine open `⊤` and `equivOfIsAffine`.
  `appTop_wordClosureι_surjective`: that global-section map is surjective,
  since `wordClosureι f` is a closed immersion and `⊤` is an affine open of `G`
  (`Scheme.Hom.app_surjective`).
- `ker_wordClosureι_le_ker`: if `wordKernel f` lies in the kernel of the
  global-section map of `g : X ⟶ G.X`, then the ideal-sheaf kernel of
  `wordClosureι f` lies in that of `g`. Over the affine `G`, ideal sheaves
  correspond monotonically to ideals of `Γ(G, ⊤)` (`Scheme.ker_of_isAffine`,
  `equivOfIsAffine`).
- `wordPoint f n : finitePower V n ⟶ wordClosure f` with
  `wordPoint f n ≫ wordClosureι f = orderedPowerMap f n` (`wordPoint_comp`):
  the factorization from `exists_over_factor_of_ker_le`, since
  `wordKernel f ≤ productKernel f n`.
- `wordPoint_appTop_eq_zero`: the global-section maps of all `wordPoint f n`
  are jointly injective. A section of `wordClosure f` lifts to `a` in
  `Γ(G, ⊤)`. If all `wordPoint f n` kill it, then `a` lies in every
  `productKernel f n`, hence in `wordKernel f`, the kernel of the lift.
- `exists_wordClosure_factor`: let `j : K ⟶ G` be a homomorphism whose
  underlying morphism is a closed immersion, and suppose `f = q ≫ j` for some
  `q`. Then `wordClosureι f` factors through `j`. Every ordered product of `f`
  factors through `j` (`orderedPowerMap_comp`), so every `productKernel f n`
  contains the global kernel of `j`. Hence `wordKernel f` does too, and
  `exists_over_factor_of_ker_le` applies.

## Multiplication and geometric reducedness

Below, `V` is `ReducedPowerGood`, so all `finitePower V n` are affine.

- `exists_mul_wordClosure`: there is `m : wordClosure f ⊗ wordClosure f ⟶
  wordClosure f` with `m ≫ ι = (fst ≫ ι) * (snd ≫ ι)`, for `ι = wordClosureι f`.
  By `ker_wordClosureι_le_ker` and `exists_over_factor_of_ker_le`, it is
  enough that every `s ∈ wordKernel f` is killed by the global-section map of
  `(fst ≫ ι) * (snd ≫ ι)`. Call that image `s'`. We apply
  `appTop_tensorHom_eq_zero` with `a = b = wordPoint f`, whose hypotheses are
  `wordPoint_appTop_eq_zero`. It then suffices that every
  `wordPoint f n ⊗ₘ wordPoint f m` kills `s'`. Now
  `(wordPoint f n ⊗ₘ wordPoint f m) ≫ ((fst ≫ ι) * (snd ≫ ι))` equals
  `appendPoint fst snd ≫ orderedPowerMap f (n + m)`, by `MonObj.comp_mul`,
  `wordPoint_comp` and `appendPoint_orderedPowerMap`. Its global-section map
  kills `s`, because `s ∈ productKernel f (n + m)`.
- `geometricallyReduced_wordClosure`: `(wordClosure f).hom` is geometrically
  reduced. By `geometrically_iff_of_isClosedUnderIsomorphisms`, we must show
  that `wordClosure f ⊗ Y` is reduced, where `Y = Over.mk x` for any field `K`
  and any `x : Spec K ⟶ Spec k`. The schemes `wordClosure f ⊗ Y` and each
  `finitePower V n ⊗ Y` are affine. Each `finitePower V n ⊗ Y` is reduced,
  since `finitePower V n` is geometrically reduced
  (`pullback_of_geometrically`). Apply `appTop_tensorHom_eq_zero` with
  `a = wordPoint f` and the one-member family `b = 𝟙 Y`. It shows that the
  global-section maps of `wordPoint f n ⊗ₘ 𝟙 Y` into the reduced rings
  `Γ(finitePower V n ⊗ Y, ⊤)` are jointly injective. So `Γ(wordClosure f ⊗ Y, ⊤)`
  has no nonzero nilpotents. An affine scheme with reduced global sections is
  reduced (`isReduced_of_isAffine_isReduced`).

## Assembly

`geometricallyReducedAffineImageGeneration` introduces the data and sets
`H = wordClosure f`.

- `G` is affine, from its affine structure morphism. `m` comes from
  `exists_mul_wordClosure`.
- The unit lift is `e = (Pi.lift Fin.elim0) ≫ wordPoint f 0`. Its composite with
  `ι` is `1`, by `orderedPowerMap_zero` and `MonObj.comp_one`.
- `H.hom = ι.left ≫ G.X.hom` is affine and locally of finite type. Hence
  `H ⊗ H` is affine and locally of finite type over `Spec k`
  (`affineFiniteType_tensor`). Its underlying scheme is therefore affine and
  locally Noetherian.
- `i = closedSubgroupHom ι m hm e he` is an actual closed subgroup inclusion
  (`isClosedSubgroup_closedSubgroupHom`). Its underlying morphism is `ι`
  (`closedSubgroupHom_hom`), which is a monomorphism.
- `f` factors through `i` via `singlePoint V ≫ wordPoint f 1`, by
  `singlePoint_orderedPowerMap`.
- Representation of `closedImageEnvelope f`, on all test objects `T`:
  - `closedImageEnvelope f ≤ range i` is `closedImageEnvelope_le`, using the
    factorization above.
  - `range i ≤ closedImageEnvelope f`: let `y ≫ ι` be a `T`-point of `range i`.
    For every closed subgroup `j : K ⟶ G` with `f = q ≫ j`,
    `exists_wordClosure_factor` gives `a` with `a ≫ j = ι`. So `y ≫ a` shows
    that `y ≫ ι` lies in `range j`.

  This gives `E : GeneratedImage f` with group `closedSubgroup ι m hm e he`,
  whose underlying object is `wordClosure f`.
- Smoothness: `(wordClosure f).hom` is geometrically reduced
  (`geometricallyReduced_wordClosure`) and locally of finite type. The group
  structure of `closedSubgroup ι m hm e he` is a `GrpObj` on
  `Over.mk (wordClosure f).hom`. Mathlib's `smooth_of_grpObj` then gives
  `Smooth (wordClosure f).hom`.
