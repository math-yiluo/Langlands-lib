# Field base change for the full derived subgroup

Authors: Worker 1484 and Worker 1449.

`Langlands.GroupScheme.derivedSubgroupFieldBaseChange` proves the exact published
proposition `DerivedSubgroupFieldBaseChangeStatement.{u}`. Its source is Milne,
*Algebraic Groups* (2017), Corollary 6.19(a), printed p.129 / PDF p.145,
registered source `milne-2017-algebraic-groups`. The official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` has no displayed correction to
this assertion. The implemented proof uses the universal closed-factorization
locus and restriction cores in place of the book's generated-subgroup argument.

The internal theorem `derivedSubgroup_baseChange_eq_of_field` works for an
affine structural map for the ambient group over any field, and an arbitrary
affine change of base from that field. It imposes no finite type condition.
It proves equality of the full subgroup functors by the two containments.
`derivedSubgroup_baseChange_le` supplies containment of the derived subgroup
after base change in the base change of the original derived subgroup:
each original closed commutator-containing subgroup pulls back to another
closed commutator-containing subgroup.

For the opposite containment, fix any closed commutator-containing subgroup
over the changed base. Its restriction core is closed representable by
`SubgroupFunctor.restrictionCore_isClosedRepresentable`, and it contains
every commutator by `ContainsCommutators.restrictionCore`. Minimality of the
original derived subgroup therefore puts it inside that core. Base change
preserves this inclusion, while `restrictionCore_baseChange_le` puts the
base change of the core inside the chosen subgroup. Intersecting over every
such subgroup gives the desired containment. This reasoning does not assume
representability of the derived subgroup itself.

For the exact target, specialize to the map `Spec K → Spec k` induced by
the algebra map for the arbitrary field extension. Equality of the functors
then transfers every exhibiting inclusion using
`IsDerivedSubgroup.baseChange_of_eq`: the pulled-back inclusion is closed
and its range is the required derived subgroup functor.

The theorem retains the arbitrary universe and all published hypotheses.
It allows imperfect fields, positive characteristic, arbitrary inseparable
or transcendental field extensions, and nonsmooth or disconnected ambient
groups. Membership and equality are tested on all schemes in the universe,
including nonaffine and nonreduced schemes; the argument does not replace
them by rational-point commutator groups.
