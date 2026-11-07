# Basic properties of points with the same image

Author: Worker 1038.

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.SameImageToolkit`, namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace`. It builds on the published definition
`SameImage` (`SameImagePoints`). Throughout, `S` is a scheme and `X : Presheaf S` is a presheaf
on schemes over `S`.

## Definitions

- `SameImage₂ a b u v`, for `a : h_U ⟶ X`, `b : h_V ⟶ X` and points `u` of `U`, `v` of `V`.
  It holds when some scheme `T` over `S` has morphisms `g : T ⟶ U` and `h : T ⟶ V` with
  `h_g ≫ a = h_h ≫ b` and a point `t` with `g t = u` and `h t = v`.
  `sameImage_iff`: `SameImage a u u' ↔ SameImage₂ a a u u'`, by definition.
- `overPullback h₁ g₂`, with projections `overPullbackFst` and `overPullbackSnd`: the pullback
  in schemes of `h₁.left` and `g₂.left`, as a scheme over `S`.
  `overPullback_condition` is its commutative square.

## Results

- `SameImage₂.refl`, `SameImage₂.symm` and `SameImage₂.trans`.
  For transitivity, a point of `overPullback` over the two given points exists by Mathlib's
  `Scheme.Pullback.exists_preimage_pullback`. The two composites to `X` agree by the two
  hypotheses and the pullback square.
- Specializations to `SameImage`: `SameImage.refl`, `.symm` and `.trans`, and
  `sameImage_equivalence`, which says that `SameImage a` is an equivalence relation on the
  points of `U`.
- `SameImage₂.of_comp`, `SameImage₂.map` and `SameImage₂.of_comp_iff`. For a morphism
  `φ : U' ⟶ U` over `S`, `SameImage₂ (h_φ ≫ a) b u v ↔ SameImage₂ a b (φ u) v`.
- `SameImage₂.exists_pullback` and `SameImage₂.of_pullback`. Let `hb` say that `b` is
  relatively representable, and take the represented pullback of `b` along `a`, with
  projections `snd` to `U` and `fst'` to `V`. Then `SameImage₂ a b u v` holds exactly when some
  point `p` of the pullback has `snd p = u` and `fst' p = v`.
  - One direction lifts the given test scheme with Mathlib's
    `Functor.relativelyRepresentable.lift'`.
  - The other uses the represented pullback as the test scheme.

Provenance: internal helpers. They express Stacks Project, Properties of Algebraic Spaces,
Section 66.4, for the Library's relation `SameImage`: points of a fibre product
lie over every pair of points with the same image. No source proof is transcribed.
