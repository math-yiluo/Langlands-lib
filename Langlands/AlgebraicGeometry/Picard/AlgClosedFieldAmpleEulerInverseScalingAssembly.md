# The `k^(2g)` scaling of the Euler product from the cube and square statements

Lean module: `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleEulerInverseScalingAssembly`,
namespace `Langlands.AbelianScheme.ScalingAssembly`.

Authors: Worker 998 (this module). It assembles units by Worker 998 and Worker 1222. Two
modules by Worker 1222 are submitted together with this one: the degree of `[k]` comes from
`Langlands.AbelianScheme.MultiplicationDegree`, and the extension from `k` nonzero in `K` to all
`k ≥ 1` comes from
`Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleEulerInverseScalingCoprimeExtension`.

## Role and provenance

This module is the conditional assembly for task `981f6bcb-41de-4a08-83b8-48b6eec2b236`,
which proves the published `Langlands.AbelianScheme.AlgClosedFieldAmpleEulerInverseScalingStatement`.
The statement says that for an ample line bundle `H` on a `g`-dimensional abelian variety `A`
over an algebraically closed field, an inverse `N` of `H`, `k ≥ 1` and an inverse `Nk` of
`H^k`,

`χ(H^k) χ(Nk) = k^{2g} χ(H) χ(N)`.

The proof follows the computation of `χ` of the Mumford bundle in the proof of Riemann–Roch
(9.11) of Edixhoven, van der Geer and Moonen, *Abelian Varieties* (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, formulas (10)-(12), printed p.132,
PDF p.136). The dual abelian variety is not used. Instead of the source's formula (9) via the
dual and the Poincaré bundle, the comparison between `H` and `H^k` is made directly on
`A ×_K A`, using the theorem of the cube (EvdGM (2.8), printed p.20, PDF p.24) and the finite
flat multiplication `[k]` of degree `k^{2g}`. This module carries out the computation when `k`
is nonzero in `K`, where the Library already proves that `[k]` is a finite flat isogeny
(`multiplication_isIsogeny_of_ne_zero`, module `FieldMultiplicationFiniteEtale`). Worker 1222's
module `AlgClosedFieldAmpleEulerInverseScalingCoprimeExtension` extends the result to every
`k ≥ 1`, so no hypothesis on `[k]` in positive characteristic is needed.

## Notation

`Z = A ×_K A` is the Library's `mumfordProduct A` (parameter-first), with projections `fst`,
`snd = q` and addition `m = mumfordAddition A`. For line bundles `L`, `M` on `A`,
`Q(L, M) = m^* L ⊗ fst^* M`. Its fibre over a point `y` of the second factor is `t_y^* L ⊗ M`.
`[k] = mulK A k` is multiplication by `k`, and `1 × [k] = mulOnSecond A k` is the lift of
`(fst, snd^k)`.

## Declarations

- `mulK`, `mulOnSecond`, `mulOnSecond_first`, `mulOnSecond_second`, `second_comp_mulK`: the
  maps above and their coordinates. `snd ≫ [k] = snd^k` is the Library's
  `points_multiplication`.
- `isPullback_mulOnSecond`: `1 × [k]` is the base change of `[k]` along `snd`. The square is
  cartesian by the pasting lemma `IsPullback.of_right`. Its composite with the defining square
  of `A ×_K A` is again that square, because `[k]` lies over the base.
- `exists_freeChart_one`: a line bundle has free charts of rank one. Its local trivializations
  are composed with Mathlib's `coproductUniqueIso`, since the free module on one generator is a
  coproduct over a one-element index.
- `eulerCharacteristic_congr_hom`: Euler characteristics along equal structure morphisms agree.
- `algClosedFieldAmpleEulerInverseScaling_of_ne_zero`: proves
  `Langlands.AbelianScheme.AlgClosedFieldAmpleEulerInverseScalingCoprimeStatement` (the target
  with the extra hypothesis `(k : K) ≠ 0`, defined in Worker 1222's module) under two
  hypotheses, both published statements whose proofs are not yet in the Library:
  - `cube : Langlands.GroupScheme.FieldCubePullbackStatement` (proof task `10d9bd97-8b97-4937-8a1a-3c96c6fb7537`);
  - `square : Langlands.GroupScheme.FieldTheoremOfTheSquareStatement` (proof task `e236fdea-a458-40b7-935e-5def16b126aa`).
- `AlgClosedFieldAmpleEulerInverseScalingReductionStatement`: the proposition
  `FieldCubePullbackStatement → FieldTheoremOfTheSquareStatement →
  AlgClosedFieldAmpleEulerInverseScalingStatement` (all at universe `u`). It is internal: it
  records exactly what this module proves, so that the reduction can be reviewed as a statement
  before the two premises are proved. It is not the target statement and does not assert either
  premise.
- `algClosedFieldAmpleEulerInverseScalingReduction`: proves the reduction statement by composing
  `algClosedFieldAmpleEulerInverseScaling_of_ne_zero` with Worker 1222's
  `algClosedFieldAmpleEulerInverseScaling_of_coprime`. Once the two premises are proved in the
  Library, the target follows by applying this theorem to their proofs.

## Proof of `algClosedFieldAmpleEulerInverseScaling_of_ne_zero`

Let `k ≥ 1` with `(k : K) ≠ 0`. Let `Hk` be the line bundle `tensorPow H k`, which is ample by the Library's
`positiveTensorPowerAmple`. Let `Q0 = Q(H, N)` and `Q1 = Q(Hk, Nk)`; these are line bundles on
`Z` (`IsLocallyFreeRankOne.tensor`). Let `E = [k]^* H ⊗ Nk` on `A`. Every line bundle on `Z` has
finite cohomology (Library `smoothProperLineBundleFiniteCohomology`, since `Z ⟶ Spec K` is
smooth and proper). The structure morphism of `Z` is `fst ≫ π = snd ≫ π`
(`pullback.condition`).

1. `χ(H^k) χ(Nk) = χ(Z, Q1)`, by shear and Künneth (`eulerCharacteristic_mumfordAddition_tensor_fst`,
   module `MumfordProductEulerCharacteristic`, Worker 1222).
2. Every `Rⁿ snd_* Q1` and `Rⁿ snd_* Q0` has finite closed support. This is
   `hasFiniteClosedSupport_higherDirectImage_mumfordAddition_tensor_fst` (module
   `MumfordSecondProjectionSupport`, Worker 1222), which uses the square theorem and the
   ampleness of `Hk` and `H`.
3. `χ(Z, Q1) = χ(Z, Q1 ⊗ snd^* E)`, by `eulerCharacteristic_twist` with `d = 1` (module
   `FiniteSupportTwistEuler`) and `exists_freeChart_one`. This is EvdGM formula (10).
4. `Q1 ⊗ snd^* E ≅ (1 × [k])^* Q0`, by `nonempty_pullback_twistedProduct_iso` (module
   `MumfordProductMultiplicationTwist`) under the cube hypothesis. So the Euler
   characteristics agree (`eulerCharacteristic_eq_of_iso`).
5. `[k]` is finite and flat by `multiplication_isIsogeny_of_ne_zero A k`, and locally of
   finite presentation over the locally noetherian `A`. Its native rank `Scheme.Hom.finrank`
   is `k^{2g}` at every point by `finrank_multiplication_eq_of_ne_zero A cube g hg H hH k`
   (module `Langlands.AbelianScheme.MultiplicationDegree`, Worker 1222; it uses the cube
   theorem, `(k : K) ≠ 0` and the ample `H`, following Milne, *Abelian Varieties*,
   Theorem 8.2).
   `eulerCharacteristic_finiteFlatBaseChange` (module `FiniteFlatBaseChangeEuler`), applied to
   the square of `isPullback_mulOnSecond` with this degree, gives
   `χ(Z, (1 × [k])^* Q0) = k^{2g} χ(Z, Q0)`. The structure morphisms `(1 × [k]) ≫ snd ≫ π` and
   `snd ≫ π` agree, because `[k]` lies over the base.
6. `χ(Z, Q0) = χ(H) χ(N)` by step 1 again.

Chaining 1-6 gives the target identity for this `k`. The axioms are `propext`, `Classical.choice` and `Quot.sound`.
