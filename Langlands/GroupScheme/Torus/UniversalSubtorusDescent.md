# Fppf descent of universal subtori

This module uses the universal-property transport and fppf torus-descent
helpers (`Torus.UniversalSubtorusTransport`, `Torus.FppfRelativeTorusDescent`).
These are derived internal constructions.

A closed subgroup whose pullbacks on an fppf cover are universal subtori is a
universal subtorus. The relative-torus property descends using
`RelativeTorus.IsTorus.of_fppfCover`. For any further base change, pull back
the original fppf cover. The commuting-square comparison identifies the
two orders of pullback, and transports the local universal property.
Containment of the range of any torus homomorphism in the closed subgroup
can be checked on this pulled-back cover. The represented-subgroup
factorization then supplies the required global homomorphism.

For a family of local universal subtori in the pullbacks of a fixed ambient
group, their pullbacks on a pairwise overlap have equal ranges: each
universal subtorus absorbs the other. Transport by the canonical ambient
comparison gives exactly the hypothesis of
`CoverDescent.isMatching_of_overlap_range_eq`.
The published fppf closed-subgroup descent construction supplies the
global closed representative. On each cover member its pullback and the
given local torus represent the same subgroup functor, so they are
isomorphic compatibly with their inclusions. Consequently the global
closed representative is a universal subtorus.

There are no assumptions of affineness, nonemptiness, reducedness or
noetherianity on the base or the covering schemes. This is the effective
descent step of the largest-subtorus construction in Conrad,
*Reductive group schemes* (2014), Remark B.1.2, pp.280–281, implemented
using all-test subgroup functors and the Library's closed-locus descent.
