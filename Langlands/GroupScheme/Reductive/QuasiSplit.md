# Field-defined geometric Borel subgroups and quasi-split reductive groups

Author: Worker 1290.

This module defines quasi-splitness for connected reductive groups over an
arbitrary field and in an arbitrary universe, using an actual field-defined
Borel inclusion. It proves elementary transport and parabolic comparisons;
it proves no Borel existence or base-extension theorem.

## Source and provenance

J. S. Milne, *Algebraic Groups* (2017), source
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`,
17.66 and 17.67, printed p. 375 (PDF p. 391). Section 17.66 specifies that a
Borel over an arbitrary field becomes a Borel over an algebraic closure.
Section 17.67 calls a connected group variety quasi-split if it contains a
Borel subgroup over the field. The retained official 2017-book errata snapshot
of 2026-11-02 was checked and has no correction to these passages.

The module restricts Milne's terminology to the connected reductive field
groups required by this program. The geometric guard below is derived
packaging needed to use the existing Library predicate faithfully.

## Definitions and scope

The existing `IsBorelSubgroup i` in `Absolute/Borel.lean` requires maximality
among smooth connected solvable closed subgroups defined over its base field.
This does not, by itself, impose geometric maximality over an arbitrary field.
Accordingly, `IsGeometricBorelSubgroup i` requires both that existing predicate
for the actual inclusion `i : B ⟶ G` over `k`, and the same predicate for its
actual base change to `AlgebraicClosure k`. The second condition supplies
geometric maximality. The first retains the existing field-level interface;
this module does not prove it follows from the second. Both inclusions are
closed subgroup schemes, and neither is replaced by a subgroup of rational
points.

`IsQuasiSplit G` has fields `isConnectedReductive : IsConnectedReductive G`
and `exists_isGeometricBorelSubgroup`, an existentially quantified actual
group scheme `B` and homomorphism `i : B ⟶ G` satisfying the geometric
predicate. Thus quasi-splitness asserts a Borel defined over `k`, rather than
only a Borel of `G` after scalar extension. No particular Borel is chosen by
the definition. There is no perfectness or characteristic assumption.

## Implemented intrinsic proofs

The imported `IsBorelSubgroup.comp_iso` from `Absolute/BorelTransport`
preserves the source smoothness, connectedness and
solvability fields, transports closedness through the ambient isomorphism,
and checks maximality by composing a larger-subgroup inclusion with the
inverse. This proof concerns only the existing Borel predicate.

`IsGeometricBorelSubgroup.comp_iso` applies this fact over `k` and over its
algebraic closure, using the base-change functor's image of the isomorphism.
`isGeometricBorelSubgroup_comp_iso_iff` applies the inverse for the converse.

`IsGeometricBorelSubgroup.isBorelSubgroup` projects the first conjunct.
`.isParabolicSubgroup` uses the same Borel after algebraic-closure base change
and the identity map as the factorization required by the existing parabolic
predicate. `IsQuasiSplit.exists_solvable_parabolic` combines this with the
Borel's solvability; it proves only this direction of Milne's solvable
parabolic comparison in 17.67.

`IsQuasiSplit.of_iso` retains the same field-defined Borel scheme and
postcomposes its inclusion with the inverse ambient isomorphism, together
with the imported reductivity transport. `isQuasiSplit_iff_of_iso` gives both
directions. No theorem here asserts arbitrary field-extension invariance.
