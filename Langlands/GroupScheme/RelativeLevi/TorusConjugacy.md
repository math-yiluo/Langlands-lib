# Local Levi conjugacy from supplied maximal tori

This is internal derived content for the proof of relative Levi conjugacy.
It packages actual maximal tori contained in specified subgroups and combines
the two named relative structure propositions, which remain explicit premises.
It does not assert the existence of such tori or prove either proposition.

`MaximalTorusInLevi l` records a commutative group scheme, a homomorphism into
the ambient group, the relative torus and closedness predicates, maximality
on every residue fibre of that ambient group, and containment of its all-test
range in the range of `l`. The definition imposes no Levi predicate on `l`.
Its base-change construction uses actual pullback group schemes and maps.
Maximality follows by applying `IsFibrewiseMaximalTorus.fieldPoint` to the
composite residue-field point and the successive-pullback comparison.
Containment and closedness persist under base change.

`range_eq_of_conjugate_maximalTori` assumes the entire
`RelativeTorusLeviStatement`, reductivity of the ambient reductive group,
relative parabolicity, both relative Levi predicates, and a maximal torus
in each Levi. If a base point of the parabolic conjugates the two supplied
torus ranges, its conjugate of the first Levi contains the second torus.
Ambient-isomorphism transport makes this conjugate a Levi. Applying
prescribed-torus uniqueness to it and to the second Levi gives the required
range equality. Every range and containment is on arbitrary test schemes.

`etaleLocallyRangeConjugate_of_maximalTori` additionally assumes the entire
`EtaleLocalMaximalTorusConjugacyStatement`. It explicitly requires the
relative parabolic and both relative Levi predicates after every change of
base. Torus conjugacy supplies an etale cover and actual points of the
base-changed parabolic. On each cover member the preceding argument
conjugates the Levi ranges. The pullback-point equivalence and
`isRangeConjugator_iff_range_baseChange_eq` convert this into the original
all-test conjugator predicate, giving `EtaleLocallyRangeConjugate` over the
original base.

The unchanged unconditional `RelativeLeviConjugacyStatement` remains open:
the two structure propositions, existence of the supplied maximal tori,
and the displayed predicate-stability input are not proved in this module.
