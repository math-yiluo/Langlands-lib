# Descent and algebraic-closure reduction for perfectness

Author: Worker 1484.

This module proves reduction lemmas for the published
`Langlands.GroupScheme.SemisimplePerfectStatement`. It does not prove that
statement without a premise. The new proposition
`AlgebraicallyClosedSemisimplePerfectStatement.{u}` names the remaining
arbitrary-universe assertion for semisimple group schemes over algebraically
closed fields.

## Implemented descent proof

`derivedSubgroup_eq_top_of_baseChange` proves that perfectness descends along
any surjective, flat, quasi-compact base morphism. There is no affineness,
smoothness, connectedness or representability hypothesis on the group or its
derived subgroup functor.

For a closed subgroup inclusion `i` containing all commutators, the defining
intersection `derivedSubgroup G` lies in `range i`. After base change, the
derived subgroup of the changed group lies in that changed intersection by
`derivedSubgroup_baseChange_le`. If the former is total, the changed range
of `i` is therefore total. A closed immersion is a monomorphism, so
`SubgroupFunctor.le_range_of_baseChange_le` descends this containment to
`⊤ ≤ range i`. Testing every such `i` gives
`⊤ ≤ derivedSubgroup G`, hence equality. This argument uses the full point
functors on all test schemes and does not replace them with rational points.

`derivedSubgroup_eq_top_of_fieldExtension` specializes the result to any
extension of fields, using `fieldExtension_fpqc`.

## Algebraic-closure reduction

`IsSemisimple.baseChange_toAlgebraicClosure` combines the published
preservation of connected reductivity under algebraic-closure base change
with preservation of finite scheme-theoretic centres under arbitrary base
change.

`semisimplePerfect_of_algebraicallyClosed` applies its explicit
`AlgebraicallyClosedSemisimplePerfectStatement` premise to the base change
over `AlgebraicClosure k` and then descends perfectness by the preceding
field-extension lemma. The input field and its algebraic closure remain in
the arbitrary universe `u`. There are no restrictions on characteristic or
perfection of the input field.

## Provenance and scope

These are internal reductions derived from the already published Library
definitions and fpqc descent results named above. Their purpose is to isolate
the algebraically closed case of the existing perfectness proof task. They
follow the algebraic-closure reduction described in the source discussion of
`Derived/SemisimplePerfectStatement.md`, but the implemented descent uses
only the elementary inclusion under base change and effective descent for
closed subgroup ranges; it does not need equality of derived subgroups
under base change or a chosen representative. No split structure, root
generation or rank-one perfectness assertion is proved here.
