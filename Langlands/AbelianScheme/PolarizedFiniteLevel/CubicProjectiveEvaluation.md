# Actual projective evaluation of the canonical cubic bundle

This internal construction specializes the actual projective frame bundle
and its evaluation, geometry and degree-one pullback constructions to
`Datum.cubicBundle` and `Datum.rigidificationModule`. It assumes the
specified finite local rank and intrinsic cubic generation. It does not
assert either of those missing geometric inputs.

For arbitrary indices `g,d,n`, `cubicProjectiveDimension g d` is
`6^g*d - 1`. Positivity of `d` makes `6^g*d` positive, even when `g = 0`,
so adding one to this projective dimension recovers the rank.
`Datum.cubicProjectiveRank` transports the supplied rank hypothesis
through this equality.

`Datum.cubicProjectiveBundle` is the actual scheme obtained by gluing
relative projective spaces over the local frames of the actual cubic
direct image. Its dimension parameter is `6^g*d - 1`.
`Datum.cubicProjectiveProjection` is its existing structure map to the
original base, and `Datum.cubicProjectiveTwistOne` is its existing global
degree-one line bundle. The projection is proper by the frame-bundle
geometry theorem.

The generation hypothesis is exactly
`EvaluationGenerates a.abelian.X.hom a.cubicBundle (𝟙 a.rigidificationModule)`.
It asserts nonvanishing of an evaluated local base section at every
point. Its proved frame criterion supplies generation in every local
frame. `Datum.cubicProjectiveEvaluation` then glues those actual local
evaluations, using identity evaluation of the full actual direct image.
Its composite with the projective projection equals the original
abelian structure map. `Datum.cubicProjectiveEvaluationOver` records
this same actual morphism in `Over S`.

`Datum.cubicProjectiveEvaluationPullbackIso` is an isomorphism of line
bundles from the pullback of the global degree-one bundle to
`a.cubicBundle`. It uses the already constructed and proved global
evaluation pullback isomorphism; it adds no compatibility hypothesis
on local degree-one comparisons. Properness of the abelian structure
map and of the projective projection proves properness of this
evaluation map.

`Datum.isClosedImmersion_cubicProjectiveEvaluation_iff` specializes the
proved target-local criterion for evaluation. It identifies closed
immersion of the actual global map with closed immersion of all the
actual local frame evaluation maps. This equivalence leaves the
local closed-immersion assertion unproved.

All schemes and morphisms remain in an arbitrary fixed universe. The
ordinary datum, polarization degree, level and per-datum dual witnesses
are unchanged. Neither local generation nor rank nor local closed
immersion is inferred from the ordinary datum alone. No moduli
representability or quotient existence conclusion is claimed.
