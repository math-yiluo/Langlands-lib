# Prescribed-torus local Levi data from the proved dynamic theorem

This module adapts the local construction and transport of `TorusDynamicLevi`,
`TorusLeviBaseChange` and `TorusLeviOverlap`.

This is an internal derived construction. It uses the published
`dynamicRelativeLevi` proof and
`radical_range_eq_of_dynamic_parabolic` to remove the universal relative
radical statement from the prescribed-torus local construction. No external
assertion is introduced. The existing constructions in `TorusDynamicLevi`,
`TorusLeviBaseChange` and `TorusLeviOverlap` retain their APIs.

`torusDynamicLeviWitnessFromDynamic` takes a reductive group scheme over any
scheme, a homomorphism `i : P ⟶ G`, a map `t : T.toGrp ⟶ P` from a commutative
group scheme, and a cocharacter `nu` of that same group. Its substantive local
hypothesis says that `i` represents the dynamic parabolic of `nu ≫ t ≫ i`.
It returns an actual `TorusLeviWitness t`: a group scheme and relative Levi
inclusion in `P`, containment of the range of `t`, and equality of ranges
for every competing relative Levi containing that range. These are statements
on every test scheme. The universe and base scheme are unrestricted. No torus
or maximality hypothesis is needed once the dynamic presentation is supplied.

The proof constructs representatives of the dynamic unipotent subgroup and
centralizer. The proved dynamic theorem supplies their radical and Levi
properties. Commutativity factors the prescribed group through the
centralizer, giving containment. For a competing Levi, its radical and the
dynamic radical have equal ranges by
`radical_range_eq_of_dynamic_parabolic`. The corresponding Levi retraction
therefore has the dynamic unipotent subgroup as its kernel. The defining
cocharacter factors through the competing Levi because the prescribed group
does. The published dynamic complement uniqueness lemma identifies its
ambient range with the centralizer, and monomorphy of the parabolic inclusion
reflects that equality to `P`. This compares radicals only in the supplied
dynamic parabolic; it does not assume `RelativeUnipotentRadicalStatement`.

`TorusDynamicPresentation.witnessFromDynamic` packages that constructor for
the existing presentation record. `TorusLeviWitness.baseChangeFromDynamic`
retains the actual pulled-back group and inclusion after any base change.
The existing `isLevi_baseChange` theorem, applied to the proved dynamics,
supplies the Levi predicate. Range base change preserves containment. The
new witness for the pulled-back dynamic presentation supplies uniqueness.

For any existing `EtaleTorusLeviData`, `overlap_range_eq_fromDynamic` pulls
back its two chosen witnesses, transports one through the canonical square
comparison, and applies uniqueness on the common ambient group. Pulling the
range equality back through that isomorphism yields the exact overlap
equality. `isMatchingFromDynamic` then invokes the published overlap-to-tests
lemma to give `CoverDescent.IsMatching` for the family of local ranges.
Neither construction takes a dynamic or radical structure statement as a
premise, because the dynamic theorem is proved (`dynamicRelativeLevi`) and the required radical
comparison is local to each dynamic presentation.

This module supplies local witnesses and matching. It does not construct a
global descended Levi or prove the unconditional prescribed-torus target.
