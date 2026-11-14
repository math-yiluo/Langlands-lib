# Effective descent of Levi representatives with a supplied radical

This module is a derived construction for the relative Levi proof program. It
combines the existing all-test subgroup representability interface, closed
subgroup effectivity in `SubgroupFunctor.ClosedCoverDescent`, and smoothness and
multiplication descent in `RelativeLevi.MultiplicationDescent`. No assertion from
external literature is introduced here.

All schemes, covering indices and group schemes are in an arbitrary universe
`u`. The base scheme is arbitrary. The cover in the descent results is an
arbitrary étale covering family; no finiteness or affineness assumption is added.

## Changes of representative

`subgroupMultiplication_comp` says that compatible maps of the two source group
schemes commute with the published multiplication morphism, in the order Levi
factor followed by radical factor. Its proof expands that multiplication and
uses the product projections and the compatibility equations.

`subgroupMultiplication_isIso_of_iso` transports isomorphy of multiplication
across compatible actual isomorphisms of both factors.

`subgroupIsoOfRangeEq` constructs a compatible isomorphism between the source
group schemes of two closed subgroup inclusions with equal all-test ranges.
Closed immersions give monomorphisms in the slice category, so each inclusion
represents its range. The existing uniqueness isomorphism for representatives
then applies. `subgroupIsoOfRangeEq_hom_comp` gives compatibility with the
inclusions.

`smooth_of_range_eq` transports smoothness of the structural morphism across
this source isomorphism. `subgroupMultiplication_isIso_of_range_eq` similarly
transports isomorphy of multiplication when the two closed factor ranges agree.
These results use equality of subgroup functors on every test scheme.

## Descent of the Levi property

`isRelativeLeviSubgroup_of_local_ranges` starts with global maps `l : L → P`
and `r : U → P`, global closedness of `l`, and the existing
`IsRelativeUnipotentRadical r`. On every cover member it takes two closed
subgroup inclusions, smoothness of the first source, and isomorphy of their
multiplication map. Their ranges must agree respectively with the base changes
of `l` and `r`.

The proof transports the local smoothness and multiplication assertions to the
actual pullbacks of the global maps. The imported étale descent theorem then
proves `IsRelativeLeviSubgroup l`, using precisely the supplied global radical.
The local second factors need only be closed; their comparison to the supplied
global radical is an explicit assumption.

## Actual representative

`LeviRepresentative F` extends `SubgroupFunctor.ClosedRepresentative F` with
`IsRelativeLeviSubgroup` for its inclusion. Its data include an actual group
scheme, an actual homomorphism to the ambient group scheme, closedness, and
representation of `F` on every test scheme.

`leviRepresentativeOfEtaleCover` takes a matching family of local subgroup
functors `F i`, actual closed representatives `lᵢ : Lᵢ → Pᵢ`, smoothness of
each `Lᵢ`, and closed second factors `rᵢ : Uᵢ → Pᵢ` with invertible
multiplication. It also takes a global relative unipotent radical `r : U → P`
and equality of the range of each pullback of `r` with the range of `rᵢ`.
It returns a `LeviRepresentative` of the existing
`SubgroupFunctor.CoverDescent.subgroup` of this matching family.

The implementation first obtains an actual global closed representative by
closed subgroup effectivity. Recovery of the local subgroup functors and the
range formula for base change give the local range equalities required by
`isRelativeLeviSubgroup_of_local_ranges`, which supplies the Levi property.

The construction retains the matching, local representability, local
smoothness, local multiplication, and global radical comparison inputs.
It does not construct a relative unipotent radical, local Levi factors, or
prescribed-torus containment or uniqueness. In particular, it is a
prerequisite for the unchanged `RelativeTorusLeviStatement`, rather than a
proof of that statement.
