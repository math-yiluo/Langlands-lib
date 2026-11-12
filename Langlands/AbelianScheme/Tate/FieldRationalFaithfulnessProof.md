# Faithfulness of the actual full rational Tate Hom map

`fieldRationalFaithfulness : FieldRationalFaithfulnessStatement.{u}` proves the
exact published target: over every algebraically closed field `Ω` of characteristic
zero, in an arbitrary universe `u`, and for every pair of actual abelian schemes `A`,
`B` over `Spec Ω`, the existing map
`rationalHomMap (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (fun _ => True)` from
`ℚ ⊗[ℤ] (A ⟶ B)` to the linear maps between the full rational Tate modules is
injective.

The theorem applies the reduction `fieldRationalFaithfulness_of_twoPowerTorsionDensity`
(proved in this module) to the published proof
`fieldTwoPowerTorsionDensity : FieldTwoPowerTorsionDensityStatement.{u}` from
`Langlands.AbelianScheme.Tate.FieldTwoPowerTorsionDensityProof`.

## Implemented proof

`exists_nsmul_eq_one_tmul` clears denominators in `ℚ ⊗[ℤ] M` for an arbitrary
abelian group `M` by tensor induction: a positive natural multiple of every element
is a pure tensor `1 ⊗ x`. Applied to `M = (A ⟶ B)`, a positive multiple `N • v` of a
rationalized Hom element is `1 ⊗ f` for an actual homomorphism `f`.

`map_eq_zero_of_rationalMap_eq_zero`: if the existing `rationalMap` of `f` at the
identity test scheme and the full positive-order torsion predicate is zero, then the
existing integral map `GroupScheme.Tate.map` of `groupHom f` kills every full
integral Tate vector. The rational image of the integral output is the rational map
applied to the rational image of the input, hence zero, and the published
`GroupScheme.Tate.full_toRational_injective` (from `FullSeparation`) for `B` makes
the integral output zero.

`levelMap_eq_zero_of_rationalMap_eq_zero`: for every positive `n`, the existing
level map `GroupScheme.Tate.levelMap` of `groupHom f` at level `n` is zero. The
published `AbelianScheme.algClosedPointDivisibility` gives `k`-th roots of every
actual geometric point for every positive `k` (the field is algebraically closed of
characteristic zero). With it, the published
`GroupScheme.Tate.full_evaluation_surjective_of_pow` makes evaluation from the full
integral Tate module onto level `n` surjective. `GroupScheme.Tate.evaluation_map`
compares evaluation of the integral map with the level map of the evaluation, and
the previous lemma makes the integral map zero.

`fieldRationalFaithfulness_of_twoPowerTorsionDensity` takes density as an explicit
premise. By the additive kernel criterion it suffices that `rationalHomMap v = 0`
implies `v = 0`. Write `N • v = 1 ⊗ f`. Additivity and `rationalHomMap_tmul` turn
the hypothesis into `rationalMap f = 0`. Every two-power level map of `f` then
vanishes, and the published `hom_eq_zero_of_dense_twoPowerTorsion` (proved in the
density statement's module from a dominant equalizer, the smooth reduced source and
the proper separated target) together with density of `twoPowerTorsionLocus A`
gives `f = 0`. Hence `N • v = 0`, and since `ℚ ⊗[ℤ] (A ⟶ B)` is a rational vector
space and `N ≠ 0`, `v = 0`.

`fieldRationalFaithfulness` discharges the density premise with the published
`fieldTwoPowerTorsionDensity`.

All statements keep the arbitrary universe `u`, the actual abelian schemes, the
identity test scheme `Over.mk (𝟙 (Spec (CommRingCat.of Ω)))`, and the full predicate
`fun _ => True`. The only axioms used are `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

The helper lemmas and the reduction are internal derived content built from the
cited Library constructions. The mathematical route (torsion points detect
homomorphisms because torsion is dense) follows Edixhoven, van der Geer, Moonen,
*Abelian Varieties*, Chapter V, Theorem (5.30), for density, and Chapter XII,
Theorem (12.10)(i), for the faithfulness of the Tate map. The density input and its
provenance are described in `FieldTwoPowerTorsionDensityStatement.md` and
`FieldTwoPowerTorsionDensityProof.md`.
