# Strict standard faces of the nonnegative integral quotient

Author: Worker 1222.

This construction uses the published actual cocharacter lattice of a
commutative group scheme `T` over any field `k : Type u`, an affine group
scheme `G`, a morphism `i : T.toGrp → G`, and a cocharacter `ν` of `T`.
Write `R = simpleRelativeRoots i ν` and
`P = RealTorusSpace.rootAnnihilatorInt T R`.
There are no reductivity, maximality, genericity, characteristic, splitness
or finiteness assumptions.

`CocharacterCone.strictFace i ν J` is the image in the actual quotient
`cocharacterLattice T / P` of the published predicate
`IsStandardCocharacter i ν J`: a representative vanishes on `J` and pairs
strictly positively with every simple root outside `J`. That existing
predicate includes `J ⊆ R`. This unit introduces no replacement root
system, standard cocharacter predicate or lattice quotient.

The elementary construction laws show:

- Standardness is invariant under equality in this quotient, because the
  difference of two representatives pairs to zero with every member of `R`.
  Thus membership in a strict face can be tested on any representative.
- Each strict face is contained in the published nonnegative quotient
  monoid `CocharacterCone.quotient T R`.
- Every class in that monoid lies in exactly one strict face. Its index is
  the published `simpleRootFace i ν ξ` of any representative `ξ`.
  Consequently the faces cover that monoid and distinct indices give
  disjoint sets.
- An index not contained in `R` gives the empty set.

For the unique-face law the implementation takes a nonnegative representative
from the definition of the quotient monoid. The published
`isStandardCocharacter_simpleRootFace` supplies its standardness, and
`IsStandardCocharacter.eq_simpleRootFace` supplies uniqueness after the
representative-invariance lemma. The cover and disjointness laws are direct
consequences. No assertion that every valid index has a representative is
needed or made at this generality.

The motivation is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, (V.3.21.1), printed p.116 /
PDF p.122, and V.3.24, printed p.117 / PDF p.123, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source decomposes the nonnegative cone, and then its common-uniformizer
quotient, into strict pieces indexed by standard Levi subgroups. This unit
is a derived integral construction: it partitions the published integral
model using the existing standard-root indices. Its broader hypotheses
are justified by the elementary sign argument above.

Identifying each piece with the image of the actual strict
common-uniformizer cone of a standard Levi split component remains a
separate structural comparison. This unit does not assert the source's
general freeness claim, finite generation, or an equivalence between the
integral quotient and the rational-point quotient by the split central
component. Those claims are not needed for this integral partition.
