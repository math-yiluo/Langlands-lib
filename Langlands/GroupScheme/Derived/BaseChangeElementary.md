# Elementary base change for the derived subgroup

Author: Worker 1484.

These internal lemmas complement the field-base-change proof of Milne,
*Algebraic Groups* (2017), Corollary 6.19(a), printed p.129 / PDF p.145,
registered source `milne-2017-algebraic-groups`. They derive directly from the
published all-test definitions in `Derived.Basic`; they assert no field
extension descent result by themselves.

`SubgroupFunctor.ContainsCommutators.baseChange` uses the multiplicative
pullback point equivalence. The equivalence maps each commutator over the
changed base to a commutator on the same test scheme viewed over the original
base. The imported `SubgroupFunctor.baseChange_mono` from
`SubgroupFunctor.FpqcDescent` transfers pointwise containment through
that equivalence.

`derivedSubgroup_baseChange_le` proves that the derived subgroup after any
base change lies in the base change of the original intersection. Given a
closed commutator-containing subgroup over the original base, its pullback is
closed (`IsClosedSubgroup.baseChange`), its range is the base change of the
original range (`SubgroupFunctor.range_baseChangeHom`), and that range still
contains every commutator. Minimality of the new derived subgroup supplies
containment in this range. Testing every original closed subgroup gives the
claimed containment. The base schemes are arbitrary and no representing
derived subgroup or finiteness hypothesis enters this argument.

`IsDerivedSubgroup.baseChange_of_eq` uses an equality of the full derived
subgroup functors to transfer any exhibiting inclusion. Its closedness follows
from preservation of closed immersions, and its range equality follows from
`range_baseChangeHom` and the original exhibiting range equality.

Every claim concerns all test schemes, including nonaffine and nonreduced
ones. The reverse containment under a field extension requires the separate
restriction-core construction. No rational-point commutator assertion is used.
