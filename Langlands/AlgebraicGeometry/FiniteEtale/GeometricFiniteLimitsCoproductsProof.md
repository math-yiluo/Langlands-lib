# Finite limits and finite coproducts of finite étale covers, preserved by the geometric fibre functor

`Langlands.AlgebraicGeometry.FiniteEtale.geometricFiniteLimitsCoproducts` proves exactly the
published target `GeometricFiniteLimitsCoproducts s hfin` from
`Langlands.AlgebraicGeometry.FiniteEtale.StructuralStatements`. It keeps the statement's
parameter list: `S : Scheme.{u}` with `[ConnectedSpace S]` and `[IsLocallyNoetherian S]`,
`Ω : Type u` with `[Field Ω]` and `[IsAlgClosed Ω]`, a point `s : Spec (.of Ω) ⟶ S`, and
`hfin : ∀ Y : Cover S, Finite (Fiber s Y)`. The six conjuncts are:

1. `HasTerminal (Cover S)`;
2. `HasPullbacks (Cover S)`;
3. `HasFiniteCoproducts (Cover S)`;
4. `PreservesLimitsOfShape (Discrete PEmpty.{1}) (fiberFunctor s hfin)`;
5. `PreservesLimitsOfShape WalkingCospan (fiberFunctor s hfin)`;
6. `PreservesFiniteCoproducts (fiberFunctor s hfin)`.

`Cover S`, `inclusion S`, `Fiber s Y`, `pointFunctor s` and `fiberFunctor s hfin` are the
published constructions of `Langlands.AlgebraicGeometry.FiniteEtale.Definitions`. The
statement pair and its imports are unchanged. The proof assumes no Galois-category
structure. Connectedness, local noetherianity and algebraic closure of `Ω` belong to the
signature but are not used. The proof uses only that `Ω` is a field.
Each conjunct is closed by `inferInstance`, from the named instances below.

The module sets `backward.isDefEq.respectTransparency.types false` for the whole file, as
Mathlib's `AlgebraicGeometry/Morphisms/Etale.lean` and `Finite.lean` do. With the option on,
instance search fails to find the `RespectsIso` and `IsZariskiLocalAtSource` instances for
`@IsFinite` and `@Etale`.

## Helpers on finite étale morphisms

- `finiteEtale : MorphismProperty Scheme.{u}` abbreviates `@IsFinite ⊓ @Etale`.
  `coverProperty_eq` records that the published `coverProperty S` is, by `rfl`, Mathlib's
  `finiteEtale.overObj`, the property of objects of `Over S` whose structure morphism is
  finite étale.
- The instance `finiteEtale_hasOfPostcompProperty` says: if `f ≫ g` and `g` are finite
  étale, then so is `f`. For finiteness it uses Mathlib's `HasOfPostcompProperty` for
  `@IsFinite` against separated morphisms (`HasOfPostcompProperty.of_le`), because finite
  morphisms are separated. For étaleness it uses the corresponding Mathlib instance for
  `@Etale`. The two are combined by the instance for an infimum of properties.
- `etale_coprod_desc` proves that `coprod.desc f g : X ⨿ Y ⟶ Z` is étale when `f` and `g`
  are. Étaleness is local on the source
  (`IsZariskiLocalAtSource.iff_of_openCover`), and Mathlib's `coprodOpenCover X Y` covers
  `X ⨿ Y` by the two coprojections. On the two pieces, the composites are `f` and `g`.

## Closure of the cover property, and the existence conjuncts

The existence conjuncts come from Mathlib's full-subcategory instances
(`hasLimitsOfShape_of_closedUnderLimits`, `hasColimitsOfShape_of_closedUnderColimits`, and
`HasFiniteCoproducts` for a property closed under finite coproducts). `Over S` has the
needed limits and colimits. So it suffices to show that `coverProperty S` is closed under
the relevant shapes.

- `coverProperty_isClosedUnderLimitsOfShape_pempty` and
  `coverProperty_isClosedUnderLimitsOfShape_cospan`: after rewriting by
  `coverProperty_eq`, these are Mathlib's `Over.closedUnderLimitsOfShape_discrete_empty` and
  `Over.closedUnderLimitsOfShape_pullback` for `finiteEtale.overObj`. Their hypotheses
  are: `finiteEtale` contains identities, respects isomorphisms, is stable under
  composition and base change, and has the postcomposition property above. Mathlib's
  instances for `IsFinite`, `Etale` and infima supply all but the last. So the terminal
  object `𝟙 S` is a cover, and a fibre product of covers over a cover is a cover.
- `coverProperty_isClosedUnderColimitsOfShape_pempty` and
  `coverProperty_isClosedUnderColimitsOfShape_pair` use Mathlib's
  `CostructuredArrow.isClosedUnderColimitsOfShape` with `P := finiteEtale` and the identity
  functor, applied to the chosen colimit cocones in `Scheme`. Then one must show that the
  descended morphism from the colimit of the underlying schemes to `S` is finite étale.
  - Empty shape: the colimit of the empty diagram is isomorphic to `⊥_ Scheme`
    (`HasColimit.isoOfNatIso D.uniqueFromEmpty`), so its underlying space is empty.
    Mathlib's instance search proves that a morphism from an empty scheme is finite and
    étale.
  - Pair shape: write `e` for the isomorphism from the colimit of `D` to the binary
    coproduct of `D.obj left` and `D.obj right` (`diagramIsoPair`). The descended morphism
    equals `e.hom ≫ coprod.desc (s.app left) (s.app right)`; this is checked on each
    colimit injection. Being finite étale is invariant under precomposition with an
    isomorphism (`MorphismProperty.cancel_left_of_respectsIso`). `coprod.desc` of two
    finite morphisms is finite by a Mathlib instance, and it is étale by
    `etale_coprod_desc`.
- `coverProperty_isClosedUnderFiniteCoproducts` follows from closure under the empty and
  binary shapes (`ObjectProperty.IsClosedUnderFiniteCoproducts.mk'`).

## Points of a coproduct of schemes

Fix a field `K` and schemes `A`, `B`.

- `exists_factor_coprod`: every `y : Spec (.of K) ⟶ A ⨿ B` factors through `coprod.inl` or
  through `coprod.inr`. `Spec K` has a unique point. Mathlib's
  `isCompl_range_inl_inr A B` says the ranges of the two coprojections are complementary,
  so the image of that point lies in one of them. Then the whole range of `y` lies in that
  range, and `IsOpenImmersion.lift` factors `y` through the coprojection, which is an
  open immersion.
- `comp_inl_ne_comp_inr`: no `a ≫ coprod.inl` equals a `b ≫ coprod.inr` for
  `a : Spec (.of K) ⟶ A` and `b : Spec (.of K) ⟶ B`. Otherwise the two composites agree
  on the point of `Spec K`, contradicting disjointness of the two ranges.

## Preservation by the point functor

The published `pointFunctor s` is definitionally
`inclusion S ⋙ coyoneda.obj (Opposite.op (Over.mk s))`. It sends a cover `Y` to
`Fiber s Y = (Over.mk s ⟶ Y.obj)`.

- Limits: `pointFunctor_preservesLimitsOfShape_pempty` and
  `pointFunctor_preservesLimitsOfShape_cospan` hold by `inferInstanceAs` for that
  composite. The inclusion of a full subcategory closed under a shape creates, and hence
  preserves, limits of that shape. Coyoneda functors preserve all limits.
- Binary coproducts: let `coverToScheme S := inclusion S ⋙ Over.forget S`, the
  underlying-scheme functor. `pointFunctorCoprodIsColimit s X Y` shows that `pointFunctor s`
  sends the coproduct cofan of `X` and `Y` to a coproduct of types. It uses
  `Types.binaryCofan_isColimit_iff`: both maps are injective and their ranges are
  complementary. Let `e` be the comparison isomorphism `PreservesColimitPair.iso` of
  `coverToScheme S`, from the scheme coproduct of the underlying schemes to the underlying
  scheme of `X ⨿ Y`. The underlying morphism of each cover coprojection is the scheme
  coprojection followed by `e.hom` (`coprodComparison_inl`, `coprodComparison_inr`).
  - Injectivity: equality of two composites in `Over S` gives equality of the underlying
    morphisms. Scheme coprojections and `e.hom` are monomorphisms and cancel.
    `Over.OverMorphism.ext` returns to slice morphisms.
  - Disjointness: this is `comp_inl_ne_comp_inr` after the same rewriting.
  - Covering: for a point `y` of `X ⨿ Y`, apply `exists_factor_coprod` to
    `y.left ≫ e.inv`. A factorisation `a` through the scheme coprojection gives
    `a ≫ (coprod.inl).hom.left = y.left`. The morphism `a` lies over `S`, because the
    cover coprojection is a morphism over `S` (`Over.w`). Then `Over.homMk a` is a point
    of `X` mapping to `y`. The right-hand case is symmetric.

  `pointFunctor_preservesColimitsOfShape_pair` turns this into preservation of the colimit
  of `pair X Y` (`preservesColimit_of_preserves_colimit_cocone`,
  `isColimitMapCoconeBinaryCofanEquiv`). It then reaches an arbitrary diagram of shape
  `Discrete WalkingPair` through `diagramIsoPair`.
- Initial object: in `pointFunctor_preservesColimitsOfShape_pempty`, the underlying scheme of
  the initial cover is initial in `Scheme`, since `coverToScheme S` preserves the initial
  object (`IsInitial.isInitialObj`). By `isInitial_iff_isEmpty` that scheme is empty.
  Hence `Fiber s (⊥_ (Cover S))` is empty: a point would send the point of `Spec Ω` into
  the empty scheme. An empty type is initial (`Types.initial_iff_empty`), and
  `preservesColimitsOfShape_pempty_of_preservesInitial` concludes.

## Transfer to the fibre functor

The published `fiberFunctor_comp_incl` states that
`fiberFunctor s hfin ⋙ FintypeCat.incl = pointFunctor s` holds by `rfl`. The fully
faithful inclusion `FintypeCat.incl` reflects limits and colimits. So
`preservesLimitsOfShape_of_reflects_of_preserves` and its colimit analogue transfer each
preservation instance from `pointFunctor s` to `fiberFunctor s hfin`
(`fiberFunctor_preservesLimitsOfShape`, `fiberFunctor_preservesColimitsOfShape`, for
any `J : Type` with `SmallCategory J`). Finally,
`fiberFunctor_preservesFiniteCoproducts` applies
`PreservesFiniteCoproducts.of_preserves_binary_and_initial` to each `Fin n`, using
`HasFiniteCoproducts (Cover S)` from above.

## Provenance

This is an internal proof of the derived target of the statement module. That module
cites Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft, Chapter
X §3, Definitions (10.25)–(10.26), printed p.150 (PDF p.154), and Theorem (10.28), printed
p.151 (PDF p.155). It isolates these finite limit and coproduct conditions from the fields
of Mathlib's `PreGaloisCategory` and `FiberFunctor`. The Lean route is internal. It
reuses Mathlib's closure results for `MorphismProperty.overObj` and for colimits in slice
categories, together with Mathlib's description of binary coproducts of schemes. It
imports the published definitions and statement by Lean name. It adds no axioms. The
instances it adds are those named above, on `finiteEtale`, `coverProperty S`,
`pointFunctor s` and `fiberFunctor s hfin`.

Worker 239 authored this proof pair.
