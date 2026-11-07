# The big cell of a split reductive group over a field

This module works in the namespace `Langlands.GroupScheme.SplitBigCell`. Its
main theorem is `isOpenImmersion_of_points`, which says that over a field k
the big-cell map

  (v, t, w) ↦ (∏_r u_{neg r}(v_r)) · i(t) · (∏_r u_{pos r}(w_r))

is an open immersion. This holds for every enumeration of the negative roots
and of the positive roots, taken with respect to a generic cocharacter ν. The
products use the order of the enumerations. The theorem is stated in terms of
points. The source C of the map is any object of `Over (Spec k)` whose points
correspond bijectively to triples of coordinates. The module reuses the
definitions `rootPoint` and `orderedProduct` of
`Langlands.GroupScheme.Reductive.LocalSplitCell`: `rootPoint u Z c` is the
point of G over Z given by u at the scalar c, and
`orderedProduct u e Z w` is the ordered product of the points
`rootPoint u (e r) Z (w r)`.

## Provenance

This module consists of internal helper results, written for the local-ring
Isomorphism Theorem task (ab10ec3c). There they give the residue-field case of
the open-immersion property of the big cell. The mathematics is the classical
big cell of a split reductive group over a field:

- J. S. Milne, *Algebraic Groups* (Cambridge, 2017), Theorem 21.84 (PDF
  page 467, printed page 451): for a split reductive (G, T) and a Borel
  subgroup B ⊇ T, the multiplication map B'_u × T × B_u → G is an open
  immersion. Milne's proof chooses a cocharacter positive on the positive roots
  and applies Theorem 13.33(d) (PDF page 281, printed page 265): for a
  cocharacter λ of a smooth group G, the multiplication map
  U(−λ) × P(λ) → G is an open immersion.
- The identification of B_u, and of U(λ) for generic λ, with the ordered
  product of the root groups in any order: Milne, Theorem 21.68(a),(c) (PDF
  page 461, printed page 445).

The Lean proof follows this route but uses the Library's own results:
`Langlands.GroupScheme.oppositeCellStatement` for the opposite cell, and the
semigroup factorization of unipotent radicals from
`Langlands.GroupScheme.Rational.DynamicRootProductRayReduction` for the ordered
products. The ordered product argument repeats the proof of the Library theorem
`dynamicRootOrderedProduct_of_splitUnipotentSourceProducts`. Here the ray
hypotheses are needed only for the single group and cocharacter at hand, so
the module states them for that group alone.

## Points of root parametrizations and of ordered products

Section `Points` works over an arbitrary commutative ring R and a group
scheme G over Spec R.

- `rootPoint_injective`: if `u : 𝔾ₐ ⟶ G` represents a subgroup functor F (so
  u is a monomorphism), then `c ↦ rootPoint u Z c` is injective for every test
  object Z. The proof cancels the monomorphism and reads off the coordinate
  (`VectorGroup.coordinates_scalarPoint`).
- `mem_iff_exists_rootPoint`: if u represents F, a point g of G over Z lies in
  F exactly when it equals `rootPoint u Z c` for some scalar c. A point of
  `𝔾ₐ` is the scalar point of its coordinate (`VectorGroup.scalarPoint_coordinate`).
- `orderedProduct_points_of_iso`: suppose groups `H r` represent subgroup
  functors `Fr r` through `j r`, and the ordered multiplication
  `∏ᶜ H ⟶ G` factors as an isomorphism `e` onto a group U followed by a
  representation `jU` of a subgroup functor F. Suppose also that each
  `u (pos r)` represents `Fr r`. Then on every test object Z, `orderedProduct
  u pos Z` is injective, and its image is the set of points of F. The proof
  writes the ordered product of root points as the image of a product point
  under `e` and `jU` (`finiteProductPointsEquiv_symm_orderedMultiplication`).
  Injectivity cancels the monomorphism `jU` and uses `rootPoint_injective` in
  each factor. Surjectivity splits a point of F through `e⁻¹` into factors and
  writes each factor as a root point by `mem_iff_exists_rootPoint`.

## Ordered products of root groups

From here on k is a field, G is a connected reductive group over Spec k,
`i : S ⟶ G` is a maximal split torus, and ν is a cocharacter of S.

- `exists_orderedProduct_of_rays`: assume the cyclic tails of distinct
  indivisible positive roots are disjoint (`hdisj`), and that a root is
  positive on ν exactly when it lies in the cyclic tail of an indivisible
  positive root (`hcover`). Let `a : Fin n → characterLattice S` enumerate the
  indivisible positive roots injectively. Then there are a group U
  representing `Dynamic.unipotent (groupHom ν ≫ i)` through `jU`, groups
  `H r` representing the root subgroups `subgroup i (a r)` through `j r`, and
  an isomorphism `e : (∏ᶜ H).X ≅ U.X` with `e ≫ jU` equal to the ordered
  multiplication of the `j r`. The proof repeats that of
  `dynamicRootOrderedProduct_of_splitUnipotentSourceProducts`. It realizes
  the positive semigroup of ν (`semigroupRealization`), computes the weight
  support of the conjugation action on U, and applies
  `hasOrderedSemigroupProducts_of_unipotent` to the root-ray blocks. It then
  identifies each block's subgroup with the root subgroup
  (`cyclicRootFunctorComparison`), and the semigroup subgroup with
  `Dynamic.unipotent` (`dynamicSemigroupComparison`).
- `ReducedRays i` (a `Prop`-valued definition): for relative roots β₁, β₂ and
  positive integers p, q, `p • β₁ = q • β₂` implies `β₁ = β₂` and `p = q`.
- `indivisiblePositiveRoots_eq`: under `ReducedRays i`, the indivisible
  positive roots for ν are exactly the roots β with `⟨β, ν⟩ > 0`.
- `exists_orderedProduct_of_reducedRays`: the conclusion of
  `exists_orderedProduct_of_rays` for any injective enumeration of the roots
  positive on ν, assuming `ReducedRays i`. Under `ReducedRays i`, both ray
  hypotheses become immediate: distinct roots have disjoint cyclic tails, and
  a positive multiple of a root positive on ν is positive on ν.
- `orderedProduct_points`: under `ReducedRays i`, let `u` be a family of maps
  `𝔾ₐ ⟶ G`, and let `pos` and `a` be enumerations of the roots positive on ν
  such that `u (pos r)` represents `subgroup i (a r)`. Then on every test
  object Z, `orderedProduct u pos Z` is injective, with image the points of
  `Dynamic.unipotent (groupHom ν ≫ i)`. This combines the two previous
  results with `orderedProduct_points_of_iso`.

## The Levi decomposition of a generic parabolic

- `parabolic_points`: let `i` be a maximal torus that is split and ν a generic
  cocharacter (`IsGenericCocharacter i ν`). Then every point g of
  `Dynamic.parabolic (groupHom ν ≫ i)` over Z is `i(t) · x` with x a point of
  `Dynamic.unipotent (groupHom ν ≫ i)`, and t and x are unique. Conversely,
  every such product lies in the parabolic. The proof first shows that the
  centralizer of ν is the image of i: `genericCentralizer` identifies it with
  the torus centralizer, and `maximalTorusCentralizer` identifies that with
  the image of i. For existence, `Dynamic.exists_hasLimit` gives the limit l
  of g, which lies in the centralizer, so l = i(t). Then `i(t)⁻¹ · g` has limit
  1 and lies in the unipotent subgroup. For uniqueness, `i(t')⁻¹ · i(t)` lies in
  both the centralizer and the unipotent subgroup, so it is 1
  (`Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent`). Since i is a closed
  immersion and hence a monomorphism, t = t'. Then x = x' by cancellation.

## The big cell

- `isOpenImmersion_of_factorization` (any base scheme B): let `iU : U ⟶ G`
  and `iP : P ⟶ G` be homomorphisms of group schemes over B, such that the
  multiplication map `U × P ⟶ G`, `(x, y) ↦ iU(x) · iP(y)`, is an open
  immersion. Let `a : C ⟶ U` and `b : C ⟶ P` be such that `z ↦ (z ≫ a, z ≫ b)`
  is bijective on points of every test object. Then `iU(a) · iP(b) : C ⟶ G` is
  an open immersion. The map `lift a b : C ⟶ U × P` is bijective on points
  (via `homEquivToProd`), so it is an isomorphism
  (`isIso_iff_yoneda_map_bijective`). The map `iU(a) · iP(b)` is its composite
  with the multiplication map.
- `bijective_cellFactors`: the bijectivity hypothesis of the previous result,
  for `U(ν⁻¹)` and `P(ν)`. Let `neg` and `an` enumerate the roots with
  `⟨β, ν⟩ < 0`, and `pos` and `ap` those with `⟨β, ν⟩ > 0`, with `u (neg r)` and
  `u (pos r)` representing the corresponding root subgroups. Let C carry
  coordinates `v₀`, `t₀`, `w₀` such that `z ↦ (z^* v₀, z ≫ t₀, z^* w₀)` is
  bijective on points of every test object Z. Let a be a point of `U(ν⁻¹)` over
  C with `iU(a) = orderedProduct u neg C v₀`, and b a point of `P(ν)` over C
  with `iP(b) = i(t₀) · orderedProduct u pos C w₀`. Then `z ↦ (z ≫ a, z ≫ b)`
  is bijective on points of every test object. The proof uses
  `orderedProduct_points` for −ν (rewritten by
  `groupHom_neg_comp_eq_oppositeCocharacter`) and for ν, and
  `parabolic_points`. Injectivity and surjectivity then reduce to the
  bijectivity hypothesis on C.
- `isOpenImmersion_of_points` (main theorem): let i be a maximal torus of G
  that is split, ν a generic cocharacter, and assume `ReducedRays i`. Take
  enumerations `neg`, `an` of the roots with `⟨β, ν⟩ < 0` and `pos`, `ap` of the
  roots with `⟨β, ν⟩ > 0`, with root parametrizations `u` as above. Let C carry
  coordinates `v₀ : Fin m → Γ(C, ⊤)`, `t₀ : C ⟶ S` and `w₀ : Fin n → Γ(C, ⊤)`
  inducing bijections of points with triples. Then the underlying scheme
  morphism of

    orderedProduct u neg C v₀ * (t₀ ≫ i) * orderedProduct u pos C w₀

  is an open immersion. The proof represents `U(ν⁻¹)` and `P(ν)` by the
  Library's affine representing objects
  (`Dynamic.Affine.isRepresentedBy_unipotentHom`,
  `Dynamic.Affine.isRepresentedBy_parabolicHom`). It applies
  `oppositeCellStatement` to get the open immersion `U(ν⁻¹) × P(ν) ⟶ G`. It
  lifts the two factors to points a and b of these groups over C, using
  `orderedProduct_points` and `parabolic_points` for membership. It then
  combines `isOpenImmersion_of_factorization` with `bijective_cellFactors`,
  and reassociates the product.

The main theorem uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.
