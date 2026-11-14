# Local conjugacy from supplied maximal tori using etale transport

This internal derived result refines the supplied-torus reduction in
`TorusConjugacy`. It retains arbitrary schemes and universe `u`, the complete
relative Levi predicates for both given inclusions, and supplied ambient
maximal tori inside their all-test ranges. The entire maximal-torus conjugacy
and prescribed-torus Levi propositions remain explicit inputs.

`etaleLocallyRangeConjugate_of_maximalTori_etale` produces an actual etale cover
with ambient points satisfying the all-test range-conjugator predicate.
Relative parabolicity supplies smoothness and affineness of the parabolic.
The supplied torus-conjugacy theorem gives the cover and points. On each cover
member, `IsRelativeParabolicSubgroup.baseChange` transports parabolicity and
`IsRelativeLeviSubgroup.baseChange_etale` transports both complete Levi
predicates along its etale covering map. Pullback preserves the supplied
maximal tori. The prescribed-torus uniqueness reduction then identifies the
two Levi ranges after conjugation. The actual pullback-point equivalence
and restriction along an identity underlying map give the original-base
all-test predicate.

The result needs no additional base-change stability premise. Its provenance
is the earlier supplied-torus argument together with the proved parabolic
and etale Levi transport lemmas. The statement of the earlier theorem and
its paired files are unchanged. This module supplies neither initial maximal
tori nor either entire structural proposition, and does not prove the
unconditional relative Levi conjugacy target.

`maximalTorusLeviConjugatorCover` uses classical choice on that proved
existence to return the actual cover and a chosen conjugator point with its
all-test certificate on every member. The choices assert no canonicity.
