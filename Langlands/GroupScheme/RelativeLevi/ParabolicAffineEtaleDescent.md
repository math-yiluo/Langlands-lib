# Effective descent of invariant parabolics over affine étale covers

This internal derived module constructs the descent of an actual relative
parabolic along a surjective étale morphism between affine schemes. The input
is a relative parabolic inclusion in the pullback of a reductive group scheme,
together with equality of its two overlap ranges after the canonical ambient
identification. The ranges are subgroup functors on all test schemes.

`IsRelativeParabolicSubgroup.exists_descent_of_overlap_range_eq` uses affineness
of the cover and of the parabolic structure morphism to obtain an affine
source group scheme. Its inclusion is monic by relative parabolicity. The
imported effective affine monic subgroup descent constructs a group scheme
over the original base, an inclusion into the original ambient group and an
actual pullback isomorphism recovering the supplied inclusion. Relative
parabolicity of the descended inclusion follows from surjective étale
detection, after transport along this isomorphism.

`ParabolicSubgroupModuli.existsUnique_of_overlap_range_eq` takes the range of
the constructed inclusion. It is an actual relative parabolic subgroup
functor whose base change is exactly the prescribed range. Fpqc injectivity
of base change on represented parabolic subgroups gives uniqueness.

`ParabolicSubgroupModuli.descendAffineEtale` selects the uniquely determined
actual parabolic subgroup from this theorem. Its base-change law gives exact
recovery of the input range, and `eq_descendAffineEtale` identifies every
parabolic with that pullback with the constructed descent.

The additional theorem
`isParabolic_of_isRepresentedBy_of_etale_surjective` detects parabolicity of
a subgroup functor with a supplied monic representative. It first compares
the pulled-back representative with a representative of the supplied local
parabolic, then applies étale detection to the original inclusion.

Affine base and cover hypotheses belong to the effective descent and
unique-existence theorems. The detection theorem for a supplied representative
does not impose them. No parameter scheme, finite classification of
parabolics or descent of a parameter scheme is constructed here. The
provenance is internal composition of actual affine monic descent,
étale detection, representing-source comparison and fpqc injectivity of
base change; no new external assertion is assumed.
