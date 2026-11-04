# A trivial maximal torus over an algebraically closed field: statement

Author: Worker 1487.

`AlgClosedTrivialMaximalTorusUnipotentStatement.{u}` concerns an
algebraically closed field `k : Type u`, a smooth connected affine group
scheme `G` over `Spec k`, and a maximal torus `i : T.toGrp ⟶ G`.
If its all-test image `SubgroupFunctor.range i` is the trivial subgroup
functor, then `IsUnipotent G`. All predicates are the existing Library
ones. The universe and characteristic are arbitrary.

This file defines a proposition and proves nothing. It is the
algebraically closed structural input to the finite-field branch of
Milne's Proposition 17.81. It does not assert that a ground-field maximal
torus remains maximal after extension.

## Derivation from the original source

Milne, *Algebraic Groups* (2017), Proposition 16.60, printed p.346
(one-based PDF p.362), says that a connected group variety over an
algebraically closed field is unipotent if it contains no nontrivial
torus. Its proof uses a closed orbit on a flag variety, the
torus–unipotent structure of a connected solvable group, and the
quasi-affineness of a quotient by a unipotent subgroup (Proposition 14.26,
printed p.286, PDF p.302). Completeness and connectedness then force
this quotient to be a point.

The present statement is a derived formulation using the published
`IsMaximalTorus`. Its closed immersion makes the range-trivial domain `T`
itself trivial. For any closed torus `j : T'.toGrp ⟶ G`, the zero
homomorphism `f : T.toGrp ⟶ T'.toGrp` satisfies `f ≫ j = i`.
Maximality says that this `f` is an isomorphism. Consequently `j` is
trivial. There is therefore no nontrivial torus in `G`, and Proposition
16.60 applies.

Smoothness supplies local finite type, and affineness over the affine
point supplies quasi-compactness, hence finite type. Thus the Lean
hypotheses give an affine group variety as in the source.
`IsUnipotent` retains its representation-theoretic, all-test meaning
from `Reductive.Basic`.

The source is registered as `milne-2017-algebraic-groups`. The full
official errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02`
was read. Its Chapter 16 entries do not change Proposition 16.60.
