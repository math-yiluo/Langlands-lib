# Effective descent of actual Levi images

This internal derived helper connects ordinary matching of actual Levi subgroup
images with the published closed-subgroup and Levi multiplication descent APIs.
The parameter scheme, base and universe are arbitrary. Equality of values is
equality of subgroup functors on all relative test schemes.

Local values use direct ambient pullbacks. The canonical comparison transports
them to iterated pullbacks. Equality under ordinary family restriction transfers
membership for points with equal projections to the original ambient group;
this supplies the all-test matching condition of `CoverDescent`. Its explicit
descended subgroup recovers each local image after actual restriction.

Two Levi images equal after an etale parameter cover are equal globally: choose
closed representatives, compare their literal base changes using the ambient
comparison, and apply the published etale-cover equality criterion for ranges.

For effectivity, the ambient group is a relative parabolic in a reductive group,
and a supplied radical has explicitly assumed stability under every parameter
base change. Choose Levi presentations and their radicals on each cover member.
Uniqueness of the relative radical identifies their ranges with the pullbacks of
the supplied radical. The published `leviRepresentativeOfEtaleCover` then descends
the closed inclusions, smoothness and the Levi multiplication isomorphisms. The
result is a Levi image of the actual explicitly descended subgroup.

The provenance is composition of the Library's actual subgroup restriction,
point adjunction, closed subgroup descent, relative radical uniqueness and Levi
descent theorems. This module does not assume a global Levi or assert arbitrary
base-change stability without its stated premise.
