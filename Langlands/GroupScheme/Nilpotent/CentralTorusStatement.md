# A central maximal torus with unipotent quotient: statement

Author: Worker 1487.

`NilpotentCentralTorusStatement.{u}` concerns a smooth connected affine
group scheme `G` over any field `k : Type u` for which the geometric
predicate `IsNilpotentGroupScheme G` holds. It asks for a commutative
group scheme `T`, a central maximal torus inclusion `i : T.toGrp ⟶ G`,
and an affine unipotent group scheme `Q` with an actual quotient
homomorphism `q : G ⟶ Q`. The quotient condition is the existing
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`.

That predicate says that the scheme morphism underlying `q` is flat,
surjective and locally of finite presentation, and that its actual
scheme-theoretic kernel represents exactly the all-test range of `i`.
It does not require `q` to be surjective on points over each test scheme.
`IsMaximalTorus` includes the torus and closed-subgroup hypotheses;
centrality uses the existing all-test `IsCentral`. The universe is
arbitrary, including finite and imperfect fields and all characteristics.

This is a proposition definition, with no proof claimed here.

## Original source and derived presentation

Milne, *Algebraic Groups* (2017), Theorem 16.47(a),(c), printed p.341
(one-based PDF p.357), constructs the largest subgroup of multiplicative
type `Z(G)_s`. It is central, its quotient is unipotent, and smoothness
of `G` makes it a torus. Since it contains every torus in `G`, it is
maximal. The statement retains those consequences, without specifying a
canonical representative or the source's stronger characteristic
property and largest-multiplicative-subgroup conclusion.

The geometric nilpotence convention is the one from `Nilpotent.Basic`:
over the algebraic closure, Proposition 16.49(a),(c), printed p.342
(PDF p.358), identifies it with nilpotence of the smooth connected
group variety. The classical central-series condition descends along
the field extension. A proof of the present statement must implement
this comparison or establish the conclusion directly from the
geometric predicate; it must not assume that comparison as an axiom.

The actual affine algebraic-group quotient has the flat, surjective
kernel-quotient properties encoded above. Smoothness and affineness of
`G` imply finite type, so this is within the source's algebraic-group
scope. Affineness of the quotient and its representation-theoretic
unipotence use the existing Library meanings.

The source is registered as `milne-2017-algebraic-groups`. The full
official errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02`
was read; its Chapter 16 entries do not alter Theorem 16.47 or
Proposition 16.49.

## Consumers

For Proposition 17.81, absence of tori makes `range i = ⊥`, so the
represented quotient is an isomorphism and `G` is unipotent.
For Theorem 17.91, the central maximal torus has centralizer all of
`G`, making the identity subgroup a Cartan subgroup.
The bad-characteristic isogeny branch of 17.80 is a separate input.
