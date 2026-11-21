# Base change of Harris level sections

This internal comparison proves that the actual global torsion sections built
from a normalized Harris orbit commute with the published Harris pullback
along a morphism of bases `b : T ⟶ S`. The pulled-back datum is
`framedPositiveActionBaseChange`, built from the dual input `W` on the
base-changed abelian scheme and the ambient frame nonemptiness at `t ≫ b`. Its
frames and fixed orbits are compared with the original ones by the published
`Tate.weilAdelicFrameBaseChange` and `Tate.weilAdelicLevelBaseChange`.
Normalization is preserved and reflected by the published
`harrisIntegralFrameCondition_baseChange` and
`harrisIntegralLevelCondition_baseChange` in `HarrisIntegralNormalizationBaseChange`.

## Base change of normalized orbits

`harrisIntegralNormalizedLevelBaseChange` is the definition of the module. For
a level `U`, it sends a normalized invariant orbit of the original datum at
`t ≫ b` to the published fixed-orbit pullback
`Tate.weilAdelicLevelBaseChange`. That pullback is a normalized orbit of the
pulled-back datum at `t` by `harrisIntegralLevelCondition_baseChange`.
`harrisIntegralNormalizedLevelBaseChange_val` records the underlying orbit.
`harrisIntegralNormalizedLevelBaseChange_injective` proves injectivity, because
on orbit classes the pullback is the inverse of the published frame-orbit
equivalence `Tate.weilAdelicFrameRightOrbitBaseChange`. Surjectivity is not
claimed. By the published equivariance, the target consists of the
normalized original orbits fixed by the image of the fundamental group of
`T`, while the map hits those fixed by the whole fundamental group of `S`.
Surjectivity of the map on fundamental groups is therefore sufficient, but
not necessary. The exact condition is that every normalized orbit fixed by
the image is fixed by the whole fundamental group of `S`.

## Pointwise comparison

`harrisIntegralFrameReduction_baseChange` holds for any field-valued point `t`
of `T`. Let `eta` be a normalized frame of the original datum at `t ≫ b`.
On the base-changed abelian scheme at `t`, the frame corresponding to `eta`
is the inverse frame base change. Its finite reduction modulo `m` is the
inverse of the published torsion base change `GroupScheme.Tate.levelBaseChange`
applied to the reduction of `eta`. For a source vector, the restricted full
Tate element of the pulled frame and the inverse integral base change of the
restricted element of `eta` have the same rational image. This follows from
the defining formula of inverse frame base change, the published compatibility
of rational and integral base change, and injectivity of rationalization.
The `m`-coordinate of inverse integral base change is inverse torsion base
change.

## Global comparison

The global theorem `harrisIntegralLevelSections_baseChange` assumes that `S` and `T` are
connected and locally noetherian and that `t` is an algebraically closed point
of `T`. It also requires the finite-fibre, torsion and unit hypotheses at
`t` and at `t ≫ b`. The standing hypotheses of the whole module remain in
force: both bases are quasi-separated, and the roots-of-unity schemes
`mu S k` and `mu T k` are finite and étale for every positive `k`. These are
the assumptions under which the published level towers are defined. For a level inside `K(m)`, let `x` be a normalized
invariant orbit at `t ≫ b`. Torsion base change carries the global section on
`T` of the pulled-back orbit to the pullback along `b` of the global section
on `S` of `x`.

The proof compares the two sides after inverse torsion base change over the
identity of `T`. Restriction to `t` is injective on global sections of the
pulled datum by `harrisIntegralGlobalTorsionEquiv`. The pulled section
restricts at `t` to the reduction of the pulled normalized frame, which
represents the pulled orbit. The pointwise comparison writes that reduction
as inverse torsion base change of the reduction of `eta`, which is the value
of the original section at `t ≫ b`. On the other side, the published
naturality `levelBaseChange_testRestrict` exchanges restriction to `t` with
base change, and the two successive restrictions compose to restriction at
`t ≫ b`.

The comparison concerns sections attached to an orbit that is already given.
It does not choose dual data, compare components of disconnected test
schemes, give fixed-degree polarizations, or construct a moduli scheme.
