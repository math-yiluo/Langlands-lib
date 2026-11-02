# Exact norm-one measure on the actual positive-central rational quotient

Author: Worker 112.

This internal construction uses the actual adelic point groups and homogeneous
quotients in `AdelicSplitCenterQuotient`, and the exact existing norm-one
quotient Haar measure in `AdelicGroupHaarMeasure`. Let `F` be a number field,
`G` an affine group scheme over `Spec F` locally of finite type,
`T` a commutative group scheme, and `i : T.toGrp ⟶ G` an actual morphism.

`positiveRationalQuotientHaarMeasure` is the pushforward of
`normOneRationalQuotientHaarMeasure F G` through the actual quotient inclusion
`normOneToPositiveQuotient`. Its definition makes no choice of a new Haar
measure, scalar or fundamental domain and does not depend on a supplied
splitting. The assertions below retain a finite split-torus isomorphism for
`T`, injectivity and finite index of the actual rational-character restriction,
and actual scheme-theoretic centrality of `i`.

These hypotheses give the previously constructed quotient homeomorphism.
The positive rational subgroup is closed, so its quotient is Hausdorff.
Polishness of the actual ambient adelic group and second countability of the
homogeneous quotient identify its inherited quotient sigma algebra with the
Borel sigma algebra of the existing quotient topology. The homeomorphism
therefore gives `positiveQuotientMeasurableEquiv` for those inherited sigma
algebras.

Both directions of this equivalence preserve the specified measures. The
inverse pushforward is exactly the old norm-one quotient measure.
`eq_positiveRationalQuotientHaarMeasure_iff` characterizes the transported
measure uniquely by this inverse normalization. Nonvanishing follows from
nonvanishing of the norm-one measure. Homeomorphic transport preserves
regularity; finiteness on compact sets and local compactness imply local
finiteness. The all-sets formula computes the transported measure by preimage
under the inclusion. Total masses are equal, and one measure is finite exactly
when the other is finite. No finite-volume input is used or established.

For every complex function on the positive rational quotient, the integral
transport identity holds for the total Bochner integral. The separate
integrability equivalence identifies precisely when the function and its
pullback are integrable, so the equality makes no unstated convergence claim.

Assuming explicitly that Haar measure on the actual norm-one group is right
invariant, the quotient measure is preserved by every positive right
translation `[x] ↦ [x * g]` for an arbitrary ambient adelic point `g`.
The proof transfers the existing norm-one translation invariance through the
measure-preserving equivalence and the previously proved translation identity
using `normOneProjection g`.

Under the same right-invariance hypothesis,
`positiveNormOneQuotientAverage` pulls the actual norm-one principal counting
average through the inverse quotient comparison. Its representative formula
uses the actual principal subgroup of the norm-one group and the constructed
projection of the representative. For every continuous compactly supported
complex function on the norm-one group, this transferred average is integrable,
and its integral is exactly the norm-one Haar integral of the original
function. The two assertions follow from the existing norm-one Weil
compatibility and the exact measure transport.

## Provenance and boundary

The argument is derived internally from the actual quotient homeomorphism,
the already constructed normalized norm-one quotient measure, and the
measurable-equivalence and regular-measure transport theorems. The implemented
proof does not select a measure from a compatibility-existence premise.

The transferred counting average is an average over the norm-one principal
subgroup. It is not asserted to be orbital integration over the uncountable
positive/principal subgroup of the full adelic group. A full-group Weil
compatibility theorem needs actual compatible measures on that subgroup and
the full ambient group, including their product and scalar normalization.
It remains separate, as do analytic unimodularity, the identification of the
supplied positive torus with Getz–Hahn's greatest Q-split centre, the existence
and character-restriction theorem for a suitable central split torus in every
connected reductive group, reduction theory and finite volume.
