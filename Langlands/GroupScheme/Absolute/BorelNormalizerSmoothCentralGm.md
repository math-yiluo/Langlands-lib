# Borel normalizer induction through smooth central quotients

Authors: Worker 1369 (implementation); Worker 1499 (smooth quotient route).

This internal construction removes the general normal-subgroup quotient
premise from the central multiplicative branch of Borel normalizer induction.
It works over an algebraically closed field at arbitrary universe `u`.
The final normalizer conclusion still assumes the smaller-Lie-dimension
induction hypothesis and a specified central closed copy of `Gm` contained
in the given Borel. It does not prove `BorelNormalizerStatement`.

`SmoothNormalQuotient.isAffineHom` applies the proved
`affineGroupSchemeQuotient` to an actual `SmoothNormalQuotient i` of a smooth
affine group. The smooth source is locally of finite type. The quotient
package records a separated, locally finite type, quasi-compact target and
a flat, scheme-surjective, quasi-compact projection, exactly the inputs of
that affineness theorem.

`exists_borel_quotients_of_smooth_central_gm` takes an actual Borel embedding
`i : B → G`, a closed central `z : Gm → G`, and a factor
`zB : Gm → B` satisfying `zB ≫ i = z`. The Borel is smooth by definition and
affine by its closed immersion into `G`. The factor `zB` is a closed
immersion because its composite with `i` is closed. Centrality gives normality
of the image of `z`; pulling back this all-test normal subgroup along `i`
gives normality of the image of `zB`.

The published `SmoothNormalQuotient.ofClosedNormal` applies to both subgroup
maps because `Gm` is smooth. It constructs actual quotient groups `Q` and
`BQ` and smooth, scheme-surjective, quasi-compact projections `q` and `p`
with their exact represented fppf kernels. The preceding affineness lemma
makes both targets affine. The published
`exists_borel_of_fppf_gm_quotients` then constructs the actual Borel
`j : BQ → Q`. It proves the commuting square, geometric connectedness of
`q`, the cartesian square and
`(SubgroupFunctor.range j).comap q = SubgroupFunctor.range i` on every
scheme test. The new existence theorem retains all these conclusions.

`centralMultiplicativeQuotientBorel` has exactly the published proposition
`CentralMultiplicativeQuotientBorelStatement.{u}` as its type. It converts
`range z ≤ center G` to `IsCentral z`, applies the preceding construction,
and uses `IsFppfQuotient.gm_induction_properties` for connectedness of `Q`
and the strict decrease `Lie.dimension Q < Lie.dimension G`. Every
conjunct of that proposition is supplied; no structural proposition is
assumed.

`normalizer_borelRange_eq_of_smooth_central_gm` uses the same quotients and
the published `normalizer_borelRange_eq_of_fppf_gm_quotient` to deduce that
the normalizer in `G(k)` of the image of `B(k)` equals that image.
It retains the induction hypothesis for every smooth, connected, affine
group with smaller Lie dimension. `borelPointOfSmoothCentralGm` chooses
an actual `B(k)` point above a rational normalizing point;
`borelPointOfSmoothCentralGm_comp` proves the exact image identity.

The provenance is internal: the proof composes the published smooth
homogeneous quotient, normal descent of the group law, represented quotient
affineness, Borel descent and Lie-dimension interfaces. Worker 1499 suggested
using the smooth normal quotient and the proved affineness theorem to avoid
the unproved general normal quotient statement. The implementation adapts
Worker 1369's earlier central-Gm construction with that replacement.
No quotient map is asserted to be surjective on points of arbitrary test
schemes. General nonsmooth normal quotient existence and the remaining
branches of Borel normalizer induction are not discharged.
