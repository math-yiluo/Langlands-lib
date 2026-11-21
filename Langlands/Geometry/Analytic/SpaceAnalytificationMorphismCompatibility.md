# Agreement of image maps on overlaps of affine test points

Author: Worker 910. The affine intersection construction used here is
Worker 790's `exists_affine_test_intersection`
(`SpaceAnalytificationAffineIntersections`).

This module proves one unconditional lemma about the published
`IsAnalytification` predicate. It is the compatibility step in the
construction of the morphism `Y' ⟶ Y` of analytifications induced by a
morphism `f : X' ⟶ X` of algebraic spaces over `Spec K`.

## Statement

`IsAnalytification.comp_map_eq_of_comp_eq` assumes:

- `X'` is separated over `Spec K` (`IsSeparated X'`). Local finite type
  is not needed.
- `f : X' ⟶ X` is a morphism of algebraic spaces.
- `(Y', p')` and `(Y, p)` are analytifications of `X'` and `X`, so `p'`
  and `p` are their families of analytic maps indexed by finite
  polynomial test points.
- `g₁ : S ⟶ (Spec A)^an` and `g₂ : S ⟶ (Spec B)^an` are morphisms in the
  localized analytic category. Here `(Spec A)^an` and `(Spec B)^an` are
  `AffineAnalytification.localized K P` and
  `AffineAnalytification.localized K Q` for finite polynomial presentations
  `P` of `A` and `Q` of `B`.
- `x` is an `A`-point and `y` is a `B`-point of `X'`, with
  `g₁ ≫ p' x = g₂ ≫ p' y`.

The lemma concludes `g₁ ≫ p (f x) = g₂ ≫ p (f y)`, where `f x` and `f y`
are the image points `RingPoints.map f x` and `RingPoints.map f y`.
Neither point needs to be étale.

## Proof

1. Since `X'` is separated, Worker 790's
   `exists_affine_test_intersection` gives a finite polynomial test algebra
   `C` with presentation `R`, and `K`-algebra maps `a : A → C` and
   `b : B → C`. Their spectra form a pullback square in algebraic spaces
   over the two test points `x` and `y`.
2. The analytification axiom `IsAnalytification.isPullback` makes the
   analytified square a pullback in the localized category. Since
   `g₁ ≫ p' x = g₂ ≫ p' y`, there is a morphism
   `c : S ⟶ (Spec C)^an` with `c ≫ (a)^an = g₁` and `c ≫ (b)^an = g₂`.
3. The pullback square commutes, so the pulled-back points agree:
   `changeRing a x = changeRing b y`. The proof compares the
   Yoneda-represented maps using `uliftYonedaEquiv_symm_map` and the
   square's commutativity `hC.w`.
4. `RingPoints.changeRing_map` lets base change of points commute with
   `f`. Hence `changeRing a (f x) = changeRing b (f y)`.
5. Rewrite `g₁` and `g₂` through `c`. The naturality axiom
   `IsAnalytification.naturality` for `p` along `a` and `b` turns both
   sides into `c ≫ p (changeRing a (f x))` and
   `c ≫ p (changeRing b (f y))`. Step 4 shows these are equal.

## Provenance: internal

This lemma is a direct consequence of the Library's definition of
`IsAnalytification`, which has a pullback axiom and a naturality axiom. It
also uses Worker 790's separated-intersection construction. In the
literature, the morphism of analytifications induced by a morphism of
algebraic spaces is defined étale-locally on charts and then glued. This
lemma is the compatibility check needed for that gluing. It does not
transcribe a separately stated result from a source.
