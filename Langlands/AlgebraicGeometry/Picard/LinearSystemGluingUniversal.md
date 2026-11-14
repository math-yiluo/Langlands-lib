# The glued universal divisor and the universal property of the glued scheme

Authors: Worker 5705.

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`), written for Task 5705. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.LinearSystemGluing`.

- `exists_open_pullback_eq_zero`, `pullback_ι_eq_zero_of_range`: Picard classes are trivial on
  small opens, and triviality transfers between open subschemes with the same image.
- `LocalData.ycover`, `LocalData.compat`, `LocalData.exists_glued_divisor`: the local divisors
  `Dp V` agree on overlaps (both restrict to `Dp (V ⊓ V')`), hence glue to an ideal sheaf `Wd` on
  `Y ×_S glued` (FLT `IdealSheafData.exists_comap_eq_of_openCover`).
- `range_testCover`, `glued_exists_point`: for a locally noetherian test `T` and a divisor `E` in
  the linear system over `T`, the local classifying points on the cover of `T` by preimages of the
  basis opens agree on transitions (universality of the local families) and glue
  (`Scheme.Cover.glueMorphismsOfLocallyDirected`) to a point `k : T ⟶ glued` with
  `Wd.comap (1 × k) = E`.
- `glued_eq_of_comap_eq`: two points of `glued` over a locally noetherian test with equal pullbacks
  of `Wd` are equal (both lift locally to the local parameters).
- `glued_isRelativeEffective`: `Wd` is relative effective Cartier
  (`RelativeEffectiveLocal.isRelativeEffectiveCartierIdeal_of_cover`).
- `glued_class` (`g` proper, flat, locally of finite presentation, geometrically integral): there is
  a class `n` on `glued` with `[O(Wd)] = [m] + [n]`
  (`PushforwardLineBundle.exists_classOf_pullback`).
- `glued_prop`: a morphism property local on the target and stable under base change holds for
  `lG` if it holds for each `pullback.snd (l i) (W i).ι`.

## Source

Kleiman, *The Picard scheme*, Theorem 3.13 and Exercise 3.14, globalized over the base.
