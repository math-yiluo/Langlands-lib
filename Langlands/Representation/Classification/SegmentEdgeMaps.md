# One-slot exactness of product induction and the edge maps of a merged slot

Author: Worker 890.

This module builds two intertwiners used in the proof of Zelevinsky 1980, 3.1
and 9.1(*) (`Langlands.Classification.SegmentFullJacquetFormula`). Let
`β = BlockShape.uniform m r hr` and let `γ = β.adjacentMerge k hk` merge the
adjacent blocks `k` and `k + 1`. Write `S = β.adjacentRefinement k hk`,
`e = β.adjacentBlockEquiv k hk` and `kk = β.adjacentMergeIndex k hk` for the
merged slot. The slot products are `Y₀ j = i_{S j}(σ (e ⟨j, 0⟩), …)`. For a
subrepresentation `W` of `Y₀ kk`, the module gives

- a surjection `i_β(σ) → i_γ(Y₀ with slot kk replaced by Y₀ kk / W)`, and
- an injection `i_γ(Y₀ with slot kk replaced by W) → i_β(σ)`.

Here `i` is the Library's normalized product induction
`T.normalizedProductInductionFunctor`. The construction does not depend on
`W` being nonzero or proper, or on any property of the factors `σ`.

All declarations live in the namespace `Langlands.Classification.SegmentEdge`.
Provenance is internal. The mathematics is the exactness of parabolic induction
(Bernstein–Zelevinsky 1977, `bernstein-zelevinsky-1977-induced-i`,
Proposition 1.9(a), printed p.445, PDF page 6) and induction in stages (same
Proposition, part (c)). These are the facts behind the edge submodules and edge
quotients that Zelevinsky 1980 (`zelevinsky-1980-induced-ii`) uses for segment
representations. The Lean proofs use Library results rather than reproving
them: the surjectivity of smooth induction, the injectivity of normalized
parabolic induction on maps, exactness of external tensor products, and the
ordered product regrouping theorem.

## Section `Update`

- `updateHom X j f`: for a family `X` of objects in categories `C i`, a slot
  `j` and `f : X j ⟶ Y`, the family morphism `X ⟶ Function.update X j Y` that
  is `f` at `j` and the identity elsewhere. The `eqToHom`s come from
  `Function.update_self` and `Function.update_of_ne`.
- `updateHomTo X j f`: for `f : Y ⟶ X j`, the family morphism
  `Function.update X j Y ⟶ X`, defined the same way.

## Section `SmoothFamilies`

General facts about morphisms of smooth representations.

- `hom_eqToHom_bijective`, `hom_iso_bijective`, `hom_iso_inv_bijective`: the
  underlying maps of `eqToHom h`, of `e.hom` and of `e.inv` for an isomorphism
  `e` are bijective.
- `comp_injective`: the underlying map of `f ≫ g` is injective if those of `f`
  and `g` are.
- `updateHom_injective`, `updateHom_surjective`, `updateHomTo_injective`,
  `updateHomTo_surjective`: if `f` is injective (resp. surjective), then every
  component of `updateHom X j f` (resp. `updateHomTo X j f`) is injective
  (resp. surjective). The component at `j` is `f` composed with an `eqToHom`.
  The other components are `eqToHom`s.

## Section `Exactness`

For a block shape `B` of `n`, the two surjectivity adapters below are
shared declarations in `Langlands.Classification`, imported from
[InducedMapSurjectivity](../Parabolic/InducedMapSurjectivity.md). They retain
the explicit field argument `F` and the explicit source and target families.
The injectivity and functor-map declarations remain in this module.


- `normalizedParabolicMap_surjective`: normalized parabolic induction
  `T.normalizedParabolicInducedMap B f` of a surjective intertwiner `f` of
  smooth representations of the Levi of `B` is surjective. This is the
  published `Induction.smoothInductionSurjectivity` applied to the twisted
  inflations to the parabolic subgroup. Its hypotheses are supplied by
  `T.generalLinearCompactOpen`, `B.isClosed_parabolic` and the smoothness of
  the twisted inflations (`isSmooth_twist_iff`, `isSmooth_comp`).
- `normalizedProductInducedMap_injective`: for blockwise injective
  intertwiners `f i`, `T.normalizedProductInducedMap B f` is injective. The
  external tensor product of the `f i` is injective
  (`FiniteTensor.externalMap_injective`), and the published
  `T.normalizedParabolicInducedMap_injective` gives the conclusion.
- `normalizedProductMap_surjective`: the same with surjective, using
  `FiniteTensor.externalMapSurjectivity` and
  `normalizedParabolicMap_surjective`.
- `productInduction_map_injective`, `productInduction_map_surjective`: the
  functor `T.normalizedProductInductionFunctor B` takes a family morphism with
  injective (resp. surjective) components to an injective (resp. surjective)
  morphism.

## Section `Edge`

Let `B` be a block shape of `n` and `k + 1 < B.length`. Write `γ`, `S`, `e` for
`B.adjacentMerge k hk`, `B.adjacentRefinement k hk` and
`B.adjacentBlockEquiv k hk`.

- `slotFamily T B k hk σ` (abbreviation): the family
  `j ↦ i_{S j}(t ↦ σ (e ⟨j, t⟩))` of smooth representations of
  `GL_{γ.size j}`. It takes values in the universe `max uF uV` of induced
  representations. At `B = BlockShape.uniform m r hr` it is by definition the
  family `slotProduct T hr k hk σ` of the separate module
  `SegmentEdgeFactorHypotheses`, which this module does not import.
- `adjacent_inner_eq`: the size casts `(B.adjacentBlock_size k hk ⟨i, j⟩).symm ▸`
  in the regrouping are trivial, because `B.adjacentBlock_size` holds by `rfl`.
- `stagesIso C D S e hs hc σ inner hinner products hproducts`: for an exact
  ordered refinement `S` of `D` regrouping the blocks of `C` along `e`, the
  isomorphism `i_C(σ) ≅ i_D(products)`. Here `inner` is any family equal
  (`hinner`) to the rank-cast family `(hs ⟨i, j⟩).symm ▸ σ (e ⟨i, j⟩)`, and
  `products` is any family equal (`hproducts`) to `i ↦ i_{S i}(inner i)`. It
  composes an isomorphism chosen from the published
  `Parabolic.orderedProductRegrouping` with the image under `i_D` of an
  `eqToIso`. This repeats the pattern of the Library's private
  `composeProductRegroupingIso` (module `HeadTailProductInduction`). Passing
  the families and equalities as arguments avoids definitional unfolding of the
  rank casts, which times out.
- `slotFamily_eq`: the inner products of the adjacent regrouping are
  `slotFamily T B k hk σ` (`rfl`).
- `regroupIso T B k hk σ`: `i_B(σ) ≅ i_γ(slotFamily T B k hk σ)`, the case of
  `stagesIso` for the adjacent merge (`B.adjacent_index` supplies `hc`). It is
  noncomputable and chosen; only its being an isomorphism is used.
- `slotQuotientMap T B k hk σ j f`: for a slot `j` and `f : slotFamily σ j ⟶ Q`,
  the composite of `regroupIso` with `i_γ(updateHom (slotFamily σ) j f)`, a
  morphism `i_B(σ) ⟶ i_γ(Function.update (slotFamily σ) j Q)`.
- `slotSubMap T B k hk σ j g`: for `g : Q ⟶ slotFamily σ j`, the composite of
  `i_γ(updateHomTo (slotFamily σ) j g)` with the inverse of `regroupIso`, a
  morphism `i_γ(Function.update (slotFamily σ) j Q) ⟶ i_B(σ)`.
- `slotQuotientMap_surjective`: if `f` is surjective, so is
  `slotQuotientMap`. Proof: `productInduction_map_surjective` with
  `updateHom_surjective`, composed with the bijective `regroupIso`.
- `slotSubMap_injective`: if `g` is injective, so is `slotSubMap`. Proof:
  `productInduction_map_injective` with `updateHomTo_injective`, then
  `comp_injective` with the bijective inverse of `regroupIso`.
- `edgeQuotientMap T B k hk σ j W` and `edgeQuotientMap_surjective`: for a
  subrepresentation `W` of `slotFamily σ j`, the case
  `f = SmoothRep.mkQ _ W` onto `SmoothRep.quotient (slotFamily σ j) W`. It is
  surjective by `SmoothRep.mkQ_surjective`.
- `edgeSubMap T B k hk σ j W` and `edgeSubMap_injective`: the case
  `g = SmoothRep.subtype _ W` from `SmoothRep.subrepresentation
  (slotFamily σ j) W`. It is injective by `SmoothRep.subtype_injective`.

## Section `Segment`

For `A` a smooth representation of `GL_r`, `β = BlockShape.uniform m r hr`,
`k + 1 < β.length`, the slot `kk = β.adjacentMergeIndex k hk` and a
subrepresentation `W` of
`slotFamily T β k hk (T.segmentFactors A m hr) kk`
(that is, of `i_{(r,r)}(ν^k A, ν^(k+1) A)` on the merged slot):

- `segmentEdgeQuotientMap T A m hr k hk W` and
  `segmentEdgeQuotientMap_surjective`: the surjection from
  `T.segmentInduced A m hr` onto
  `i_γ(Function.update (slotFamily …) kk (slot / W))`. It is `edgeQuotientMap`
  at `σ = T.segmentFactors A m hr`, using that `T.segmentInduced A m hr` is by
  definition `i_β(T.segmentFactors A m hr)`.
- `segmentEdgeSubMap T A m hr k hk W` and `segmentEdgeSubMap_injective`: the
  injection of `i_γ(Function.update (slotFamily …) kk W)` into
  `T.segmentInduced A m hr`, the case `edgeSubMap`.

These are the maps `Π_k ↠ i_γ(Y_L)` and `i_γ(Y_W) ↪ Π_k` of the edge
argument. `Y_L` and `Y_W` are `Function.update Y₀ kk (quotient Y₀ kk W)` and
`Function.update Y₀ kk W`. The Jacquet modules of `i_γ(Y_L)` and `i_γ(Y_W)`
are the subject of the published statement `SegmentEdgeJacquetFiltration` and
of the factor hypotheses module `SegmentEdgeFactorHypotheses`. This module
only builds the maps.
