# Diagonals of presheaves through equalizer loci

Author: Worker 766.

This module is in the namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`. It
works with an arbitrary presheaf `F : Presheaf S` on schemes over a scheme `S`, in
the Library's convention `Presheaf S = (Over S)ᵒᵖ ⥤ Type (u + 1)`, with the
represented presheaves `schemeYoneda S`. No sheaf condition, group structure or
finiteness hypothesis is assumed.

The pullback of the diagonal `F ⟶ F ⨯ F` along a pair of points `x y` of `F` over
a scheme `U` is the locus of `U` where `x` and `y` agree. The module turns this
standard fact into a sufficient criterion and a converse, for a morphism
property `P` of schemes. Suppose that `P` respects isomorphisms. If every such
locus is cut out, in the factorization sense of `RepresentsEqualizer` below, by a
morphism whose underlying scheme morphism is a monomorphism with `P`, then the
diagonal is representable with every represented projection in `P`. Conversely,
for any `P`, if the diagonal is representable with projections in `P`, then every
such locus is cut out in this factorization sense by a morphism with `P`. The weaker factorization
condition alone, without the monomorphism, is not claimed to be equivalent to
representability of the diagonal.

## A categorical pullback square

`isPullback_diag_of_isLimit_fork` holds in any category with the binary product
`Y ⨯ Y`. Let `c` be a limit fork of `f g : X ⟶ Y`, with inclusion `c.ι`. Then the
square

```text
c.pt ---c.ι ≫ f---> Y
  |                 |
 c.ι              diag Y
  v                 v
  X --prod.lift f g--> Y ⨯ Y
```

is a pullback square. This is the usual description of the pullback of the
diagonal as an equalizer. Mathlib states a related comparison as
`isPullback_equalizer_prod`; the version here is proved directly from the
universal property of `c`.

## Equalizer loci cut out by factorization

`RepresentsEqualizer ι x y` is the definition of this module. Here `ι : Z ⟶ U` is
a morphism in `Over S` and `x y : F.obj (op U)`. It says that for every test object
`T : Over S` and every `g : T ⟶ U`, `g` factors through `ι` exactly when the
restrictions `F.map g.op x` and `F.map g.op y` are equal. The factorization is
only required to exist, not to be unique, and `ι` is not required to be a
monomorphism. So the definition says that the image of the map of represented
presheaves induced by `ι` is the subfunctor of the presheaf represented by `U`
on which `x` and `y` agree. It does not by itself say that `ι` represents this
subfunctor. For example, with `S = U = Spec ℚ`, `F` the terminal presheaf and
`x = y`, the fold map `U ⊔ U ⟶ U` satisfies the definition, but `𝟙 U` has two
different lifts. When `ι` is in addition a monomorphism, the lifts are unique,
and then `ι` does represent the subfunctor. The results below add the
monomorphism hypothesis where it is needed, for `ι` in `Over S` or for the
underlying scheme morphism `ι.left`.

`schemeYoneda_app_up` is a small evaluation lemma. A natural transformation
`α` from the presheaf represented by `U` to `F` sends the morphism `g : T ⟶ U` to
`F.map g.op` applied to the point of `F` over `U` that corresponds to `α` under
Mathlib's `uliftYonedaEquiv`.

`RepresentsEqualizer.isLimitFork` takes two natural transformations `α β` from
the presheaf represented by `U` to `F`, and a monomorphism `ι` in `Over S` with
`RepresentsEqualizer ι` for their Yoneda points. Given the commutation
`schemeYoneda S |>.map ι ≫ α = schemeYoneda S |>.map ι ≫ β`, it builds a limit
fork of `α` and `β` with inclusion the represented map of `ι`. The proof checks
limits objectwise (`evaluationJointlyReflectsLimits`) and uses Mathlib's
criterion `Types.typeEqualizerOfUnique` for equalizers of types. Existence of the
lift is the factorization given by `RepresentsEqualizer`. Uniqueness is
cancellation of the monomorphism `ι`.

## The criterion and its converse

`relative_diag_of_representsEqualizer` takes a morphism property
`P : MorphismProperty Scheme` that respects isomorphisms. Its hypothesis is that
for every `U : Over S` and all `x y : F.obj (op U)` there are `Z : Over S` and
`ι : Z ⟶ U` such that `ι.left` is a monomorphism of schemes,
`RepresentsEqualizer ι x y` holds, and `ι.left` has `P`. Both the monomorphism
hypothesis and the hypothesis that `P` respects isomorphisms are part of the
theorem. The monomorphism property of `ι.left` makes `ι` a monomorphism in
`Over S`, which gives the uniqueness of lifts used by the limit fork above. The conclusion is

```text
(MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S) (diag F),
```

the Mathlib property that the diagonal is relatively representable with every
represented base change in `P`. The proof uses `MorphismProperty.relative.of_exists`.
Given `g` from the presheaf represented by `U` to `F ⨯ F`, it applies the
hypothesis to the two Yoneda points of `g ≫ prod.fst` and `g ≫ prod.snd`. It then
combines the limit fork above with `isPullback_diag_of_isLimit_fork`, rewriting
`prod.lift (g ≫ prod.fst) (g ≫ prod.snd) = g`.

`exists_representsEqualizer_of_relative_diag` is the converse. It needs no
hypothesis on `P`. If the diagonal is relatively representable with projections
in `P`, then for all `x y : F.obj (op U)` there is some `ι : Z ⟶ U` with
`RepresentsEqualizer ι x y` such that `ι.left` has `P`. The statement does not
record that `ι` is a monomorphism. The locus is the chosen
pullback of the diagonal along `prod.lift` of the two Yoneda maps. The two
directions of the factorization condition come from the commutativity of the
pullback square and from its lifting property, together with full faithfulness of
`schemeYoneda S`.

## Corollaries

Each corollary specializes the criterion. Here `IsImmersion` and
`AlgebraicGeometry.IsClosedImmersion` are Mathlib's properties of scheme
morphisms.

- `hasRepresentableDiagonal_of_representsEqualizer`: if for all `x y` there is
  some `ι` with `RepresentsEqualizer ι x y` whose underlying scheme morphism is a
  monomorphism, then
  `HasRepresentableDiagonal F` holds. This is the Library's representability of
  the diagonal, from `AlgebraicSpace/Basic.lean`. The proof takes `P` to be the
  monomorphisms.
- `relative_isImmersion_diag_of_representsEqualizer`: if for all `x y` there is
  some `ι` with `RepresentsEqualizer ι x y` such that `ι.left` is an immersion,
  then the diagonal is relatively representable with
  all projections immersions. Immersions are monomorphisms, so the monomorphism
  hypothesis is supplied automatically. That `IsImmersion` respects isomorphisms
  follows from its stability under base change.
- `isClosedImmersion_diag_of_representsEqualizer`: if for all `x y` there is
  some `ι` with `RepresentsEqualizer ι x y` such that `ι.left` is a closed
  immersion, then `IsClosedImmersion (diag F)` holds. This
  is the Library predicate of `AlgebraicSpace/Thickening.lean`, which is by
  definition the relative property above for Mathlib's closed immersions.

## Provenance and scope

This is an internal helper for the diagonal branch of the proof of
`FieldPicardSheafAlgebraicSpaceStatement`. It is derived from the standard
categorical fact that a base change of the diagonal is an equalizer, applied to
the Library's presheaves on `Over S`. No separate literature theorem is claimed.
The module proves nothing about Picard sheaves. Showing that the equalizer loci of
the Picard sheaf are cut out in this sense by immersions or closed immersions is
separate work.
