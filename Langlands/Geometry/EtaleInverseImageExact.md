# Exact inverse image for arbitrary morphisms of schemes

This internal construction proves exactness of the existing
`Langlands.Geometry.EtaleInverseImage.inverseImage f R` for every morphism
`f : Z ⟶ X` of `Scheme.{u}` and every commutative ring `R : Type u`.
Coefficients remain `ModuleCat.{u} R`. There is no affine, etale,
finite-type, Noetherian, field, finiteness, freeness or local-constancy
hypothesis. The construction does not replace the existing inverse image.

The proof combines the actual affine-base exactness from
`EtaleInverseImageAffineExact`, the constructed composition and etale
restriction comparisons, and conservativity of restriction to a covering
family from `EtaleRestrictionCover`. It uses the canonical affine open cover
and its actual scheme-theoretic pullback.

## The local geometric comparison

For schemes `X`, `Z`, `Y`, `W`, maps `f : Z ⟶ X`, `i : Y ⟶ X`,
`j : W ⟶ Z`, `g : W ⟶ Y`, and a proved equality
`h : j ≫ f = g ≫ i`, assume that `i` and `j` are etale.
`inverseImageRestrictionSquare R f i j g h` constructs the natural
isomorphism

```text
inverseImage f R ⋙ restriction j (ModuleCat R)
  ≅ restriction i (ModuleCat R) ⋙ inverseImage g R.
```

The square need only commute for this comparison. No cartesian hypothesis
is required. The isomorphism first replaces restriction along `j` by the
existing constructed inverse image, applies `inverseImageComp`, transports
along the actual equality `h` with `inverseImageCongr`, reverses composition
along `i` and `g`, and finally replaces inverse image along `i` by
restriction. All five factors are existing constructed natural
isomorphisms. In particular the desired local comparison is not an input.

## Actual covers and affine local exactness

`affineEtaleCover X` is `X.affineCover` viewed as a cover for
`Scheme.precoverage (@Etale)`. Its component schemes are affine, and its
component maps are open immersions and hence etale. The instances
`affineEtaleCover_map_etale` and `affineEtaleCover_isAffine` expose the latter
two facts needed by the proof.

`pulledBackAffineCover f` is the genuine `pullback₂` of this cover.
Its component schemes and structure maps are

```text
V_i = pullback ((affineEtaleCover X).f i) f
j_i = pullback.snd ((affineEtaleCover X).f i) f : V_i ⟶ Z.
```

This is an actual etale cover of `Z`, including its proved covering
condition; the components `V_i` need not be affine. Write
`g_i = pullback.fst ((affineEtaleCover X).f i) f`.
The target of `g_i` is the affine scheme `(affineEtaleCover X).X i`.
The pullback equation, with its orientation reversed, supplies the
commuting-square equality above. The resulting isomorphism is
`inverseImageAffineLocalIso`.

The functor `restriction ((affineEtaleCover X).f i) (ModuleCat R)` preserves
limits by its previously constructed left adjoint.
The functor `inverseImage g_i R` preserves finite limits by the affine-base
result. Thus their composite preserves finite limits, and transport along
`inverseImageAffineLocalIso` gives the instance
`inverseImageAffineLocal_preservesFiniteLimits`. This step imposes no
affineness on `Z` or on the pulled-back component `V_i`.

## Detecting finite limits globally

The private helper `productIsLimit` constructs the limiting lift in a
product category from the limiting lifts in each component. Its
factorization and uniqueness proofs are pointwise. Its universes are kept
independent to accommodate the actual sheaf categories and the scheme
cover index. This is the usual product-category universal-property
argument, implemented directly.

The functor consisting of `inverseImage f R` followed by the actual family
restriction to `pulledBackAffineCover f` therefore preserves finite limits:
each component has the finite-limit property just proved. This is the
instance `inverseImage_restrictedFamily_preservesFiniteLimits`.

The family restriction reflects finite limits by
`EtaleRestrictionCover.restrictionFamilyReflectsFiniteLimits`. Its
`CoversTop` hypothesis is furnished by the actual scheme cover through
`coverObjects_coversTop`. Hence Mathlib's
`preservesFiniteLimits_of_reflects_of_preserves` proves
`inverseImage_preservesFiniteLimits` for the original inverse image.
Finite-limit preservation is proved locally and detected globally; it is
not deduced from the existence of the affine Kan extension alone.

## Exported exact functor and comparisons

For any finite category `J` in an independent diagram universe,
`inverseImageLimitIso R f F` is the canonical natural finite-limit
comparison supplied by `preservesLimitIso`:

```text
(inverseImage f R).obj (limit F) ≅ limit (F ⋙ inverseImage f R).
```

`inverseImageExactFunctor R f` packages the original functor using
`ExactFunctor.of`. The new result supplies finite-limit preservation;
finite-colimit preservation follows from the previously constructed actual
inverse/direct-image adjunction. In the abelian categories of module
sheaves this is exactness. The final `rfl` lemma
`inverseImageExactFunctor_obj` states that the underlying functor is
definitionally the existing `inverseImage f R`.

This module establishes ordinary exactness of geometric inverse image. It
does not supply coefficient-extension or algebraic-closure comparisons,
equivariant or smooth-action adapters, support conditions, derived
comparisons, or the Harris specialization.
