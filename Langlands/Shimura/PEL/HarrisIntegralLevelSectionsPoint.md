# Independence of the reference point for Harris level sections

This internal comparison shows that the actual global torsion sections built
from a normalized Harris orbit, and the ordered full level built from them,
do not depend on the geometric reference point. The point change is the
published path transport of Weil-compatible frames and fixed orbits,
`Tate.weilAdelicFrameTransport` and `Tate.weilAdelicLevelTransport`. Its
preservation of normalization is the published
`harrisIntegralFrameCondition_point` and `harrisIntegralLevelCondition_point`.
No path is chosen here: the path is an explicit argument of each comparison.

The module uses the published equivalence of normalized invariant orbits
`harrisIntegralNormalizedLevelPointEquiv`. It is the restriction of
`Tate.weilAdelicLevelTransport` to normalized orbits, by
`harrisIntegralLevelCondition_point`, from
`HarrisIntegralNormalizationPointComparison`. No new orbit transport is
defined here.

`harrisIntegralFrameReduction_point` compares finite reductions. Let `eta` be
a normalized frame at `s`, transported along a fibre-functor isomorphism to
`t`. For a source vector, the restricted full Tate element of the
transported frame is the integral path transport of the restricted element
of `eta`. Both have the same rationalization by the published
`Tate.toRational_transport` and the characterizing equation of the
restriction, and rationalization is injective on the full Tate group. The
`m`-coordinate of integral path transport is the finite path transport on
actual `m`-torsion. Hence the reduction of the transported frame is finite
path transport composed with the reduction of `eta`, on every class of the
source quotient.

`levelTransport_levelRestrict_global` is the corresponding statement for a
global `m`-torsion section `v`. A private helper with the same argument
exists inside `HarrisIntegralOrderedFullLevel`; this public version is
needed by the comparisons below. By the kernel universal property, `v` is a
morphism from the identity cover to the actual torsion cover, and its value
at a point is precomposition with that point. Naturality of the path at
this morphism, together with the fact that the identity-cover fibre at `t`
has only one element, shows that transport of the value at `s` is the value
at `t`.

`harrisIntegralLevelSections_point` takes geometric points on a connected
locally noetherian base and a transporter level contained in `K(m)`. For a
normalized invariant orbit at `s` and its transported orbit at `t`, the two
additive maps `harrisIntegralLevelSections` agree on every class of the
source quotient. Restriction to `t` is injective on global torsion sections
by `harrisIntegralGlobalTorsionEquiv`, so it suffices to compare values at
`t`. The value of the section of the transported orbit is the reduction of
the transported normalized frame, which represents the transported orbit.
By the frame comparison, this equals path transport of the reduction of
`eta`. That reduction is the value at `s` of the section of the original
orbit, and the restriction lemma moves this value to `t`.

`harrisIntegralOrderedFullLevel_point` concludes that the ordered sections of
`harrisIntegralOrderedFullLevel` coincide for the two points, since each
ordered section is the global section of the same source residue class.
`harrisIntegralOrderedFullLevel_normalizedTransport` restates this for a
normalized orbit and its image under the published
`harrisIntegralNormalizedLevelPointEquiv`.

This module does not treat base change along morphisms of test schemes,
fixed-degree polarizations, the comparison of whole moduli functors or
representability.
