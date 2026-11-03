# Concatenated points and schematic dominance of image factorizations

This internal helper module supplies the point manipulations and dominance
facts used in `ImageGenerationPointed`. It formalizes no literature assertion.
It is assembled from the published `finitePower`/`orderedPowerMap` API and from
Mathlib's scheme-theoretic image, schematic dominance, flat base change and
geometric-property APIs. Everything is in universe `u`.

## Points of finite powers

Work over an arbitrary base `B`, with an actual group scheme `G : GroupScheme B`
and `V : Over B`. All statements hold for morphisms from an arbitrary test
object `T : Over B`.

- `appendPoint x y`: concatenates an `a`-tuple `x : T ⟶ finitePower V a` and a
  `b`-tuple `y : T ⟶ finitePower V b` into an `(a + b)`-tuple, using
  `Fin.append` on the coordinates.
- `appendPoint_orderedPowerMap`: the ordered product of the concatenation is the
  product, in this order, of the two ordered products. The proof uses
  `orderedPowerMap_points`, `List.ofFn_add` and `List.prod_append`.
- `constPoint v n`: the constant `n`-tuple at `v : T ⟶ V`.
  `constPoint_orderedPowerMap`: if `v ≫ f = 1`, its ordered product is `1`.
- `singlePoint V : V ⟶ finitePower V 1` is the diagonal one-tuple.
  `singlePoint_orderedPowerMap`: its ordered product under `f` is `f`.
- `padMap v n m : finitePower V n ⟶ finitePower V (n + m)` appends `m` copies of
  a unit point `v : 𝟙_ (Over B) ⟶ V`. `padMap_orderedPowerMap`: if `v ≫ f = 1`,
  then `padMap v n m ≫ orderedPowerMap f (n + m) = orderedPowerMap f n`.
- `exists_over_factor_of_ker_le i g h`: let `i : X ⟶ Z` be a morphism in
  `Over B` whose underlying morphism is a closed immersion, and let
  `g : Y ⟶ Z`. If the ideal-sheaf kernel of `i.left` is contained in that of
  `g.left`, then `g` factors through `i` in `Over B`. The proof applies
  Mathlib's `IsClosedImmersion.lift` to the underlying morphisms and checks
  compatibility with the structure morphisms.

## Schematic dominance

- `isSchemeTheoreticallyDominant_toImage f`: for a quasi-compact morphism of
  schemes `f : X ⟶ Y` with `Y` affine, the factorization `f.toImage` through the
  scheme-theoretic image is schematically dominant. The image is affine, being
  closed in `Y`. Mathlib's `toImage_app_injective` gives injectivity on global
  sections. By `IdealSheafData.ext_of_isAffine` and `Scheme.Hom.ker_apply`, this
  makes the kernel of `f.toImage` zero.

Over an arbitrary base `B`:

- `isSchemeTheoreticallyDominant_whiskerRight t R` and
  `isSchemeTheoreticallyDominant_whiskerLeft t R`: for `t : X ⟶ Y` in `Over B`,
  suppose `t.left` is quasi-compact and schematically dominant and `R.hom` is
  flat. Then the underlying morphisms of `t ▷ R` and `R ◁ t` are schematically
  dominant. Each whiskered morphism is a base change of `t.left` along a flat
  projection. This follows by pasting the pullback squares of
  `X ⊗ R ⟶ R` and `Y ⊗ R ⟶ R`, after which Mathlib's
  `IsSchemeTheoreticallyDominant.of_isPullback` applies.
- `isSchemeTheoreticallyDominant_tensorHom t`: if moreover `X.hom` and `Y.hom`
  are flat, then `(t ⊗ₘ t).left` is schematically dominant. The morphism is the
  composite `(t ▷ X) ≫ (Y ◁ t)`, and schematic dominance is stable under
  composition.

## Descent of geometric properties

- `irreducibleSpace_of_denseRange`: a continuous map with dense range from an
  irreducible space has irreducible target.

Let `S` be a one-point integral scheme, such as `Spec k` for a field `k`. Let
`p : X ⟶ Y` be quasi-compact and schematically dominant, and `g : Y ⟶ S`.

- `geometricallyReduced_of_isSchemeTheoreticallyDominant p g`: if `p ≫ g` is
  geometrically reduced, so is `g`.
- `geometricallyIrreducible_of_isSchemeTheoreticallyDominant p g`: if `p ≫ g` is
  geometrically irreducible, so is `g`.

For a field point `x : Spec K ⟶ S`, Mathlib's `pullbackRightPullbackFstIso`
identifies the fibre of `p ≫ g` with the pullback of `p` along the fibre
projection of `g`. Every morphism to `S` is flat, by Mathlib's instance for
one-point integral targets. In particular `x` is flat, hence so is its base
change, the projection from the fibre of `g` to `Y`. The base change of `p`
along this flat projection is therefore again quasi-compact and schematically
dominant. For reducedness, Mathlib's
`IsSchemeTheoreticallyDominant.isReduced` shows that the fibre of `g` is
reduced. For irreducibility, the base change of `p` is dominant, so the fibre
of `g` is the closure of the image of an irreducible space.

No separability, perfectness or characteristic hypothesis is used.
