# The stabilizer of a section is a closed subgroup scheme

Author: Worker 1399. This is a helper module for the proof of
`Langlands.GroupScheme.SomeBorelQuotientProperStatement` (task
`26c798aa-c7cc-4a23-94b9-235cc57dc70c`). It is step (C) of the plan by
Worker 1396: the stabilizer of the fixed point on a closed orbit is a closed
subgroup whose points are exactly the stabilizing points.

## Setting

Fix a base scheme `S`, a group scheme `G` over `S`, a scheme `X` over `S`, an
action `a : SchemeAction G X` (the Library's module-object action), and a section
`x : 𝟙_ (Over S) ⟶ X`. For a test scheme `T` over `S`, `x_T = toUnit T ≫ x` is the
pullback of `x` to `T`.

## Contents

- `stabilizer a x : SubgroupFunctor G` has as `T`-points the `g : T ⟶ G.X` with
  `a.act g x_T = x_T`. It is a subgroup by `act_one` and `act_mul`; for inverses,
  `g⁻¹ • x_T = g⁻¹ • (g • x_T) = (g⁻¹ g) • x_T = x_T`. It is stable under change of
  test scheme by `SchemeAction.naturality` and `b ≫ toUnit T = toUnit T'`.
  `mem_stabilizer` unfolds membership.
- `orbitMap a x = a.act (𝟙 G.X) (toUnit G.X ≫ x) : G.X ⟶ X` is the orbit map. This is
  existing morphism from `SchemeActionRationalPoints`, also used by Worker 716's
  `OrbitMapFaithfullyFlatStatement`. The imported `comp_orbitMap` says `g ≫ orbitMap = g • x_T`,
  by naturality.
- `stabilizerScheme a x` is the equalizer, in `Over S`, of the orbit map and the
  constant map `toUnit G.X ≫ x`. `stabilizerι a x` is its inclusion into `G.X`.
- `mem_stabilizer_iff_factors`: `g` lies in the stabilizer iff it factors through
  `stabilizerι`. The equalizer's universal property gives this, because
  `g ≫ orbitMap = g • x_T` and `g ≫ toUnit G.X ≫ x = x_T`.
- `stabilizer_isClosedRepresentable`: if `X.hom` is separated, the stabilizer is
  represented by a closed subgroup scheme. The equalizer inclusion is a closed
  immersion by Mathlib's `isClosedImmersion_equalizer_ι_left`, and it is a
  monomorphism. The Library's `SubgroupFunctor.isClosedRepresentable_of_scheme`
  then supplies the group scheme and the homomorphism.
- `exists_isClosedSubgroup_stabilizer`: the same fact as an existential. If `X.hom`
  is separated, there are a group scheme `H` and `iH : H ⟶ G` with
  `IsClosedSubgroup iH`, such that for every test `T` and every `g : T ⟶ G.X`,
  `g` lies in `range iH` iff `a.act g x_T = x_T`. Step 4 of
  `someBorelQuotientProper_of_prerequisites` (module
  `Langlands.GroupScheme.Absolute.BorelProperQuotientReduction`) uses this form.
- `isFixed_restrict_iff`: for a homomorphism `iK : K ⟶ G`, the restricted action
  fixes `x` on all tests (`SchemeAction.IsFixed`) iff `range iK ≤ stabilizer a x`.
  The direction from `IsFixed` takes the test morphism `toUnit T`. The converse
  uses the fact that any morphism to `𝟙_` equals `toUnit`.

## Provenance

This is the standard fact that the stabilizer of a point is the fibre of the orbit
map over that point. See J. S. Milne, *Algebraic Groups* (2017), source
`milne-2017-algebraic-groups`: the stabilizer `G_x` is a closed
subgroup when `X` is separated. Here it is proved directly as an equalizer. No
field, finiteness or smoothness hypothesis is needed.
