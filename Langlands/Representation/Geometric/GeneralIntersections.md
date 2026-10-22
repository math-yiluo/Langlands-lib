# General geometric-lemma intersection data

This module constructs the subgroup geometry and character predicates used in
Bernstein--Zelevinsky (1977), section 5.1. It neither states nor proves the
geometric lemma. The groups are arbitrary groups for the algebraic constructions,
and arbitrary topological groups for the continuity and closedness results.
The coefficient monoid has an independent universe and need not have a topology.
In the source application it is the group of nonzero complex scalars.

The existing `Langlands.Geometric.intersectionSource`,
`intersectionTarget`, and `intersectionConjugation` in
`Langlands.Representation.Geometric.WeylDefinitions` already construct the
ambient intersections and their conjugation equivalence for arbitrary groups.
They are reused here; their surrounding GL-specific definitions are not
hypotheses of these constructions.

## Actual intersections and conjugation

`conjugate H w` is the actual subgroup `w H w⁻¹`. Its membership formula
and its description as the image of elements of `H` are proved.

`intersectionIn M K w` is a subgroup of `M`, consisting of the elements
whose conjugates by `w` belong to `K`. Thus the source parabolic, Levi and
radical intersections in section 5.1 are respectively

- `intersectionIn M Q w`,
- `intersectionIn M N w`,
- `intersectionIn M V w`.

The target groups are obtained by interchanging the two triples and replacing
`w` with `w⁻¹`. In particular the target Levi is
`intersectionIn N M w⁻¹` and the target radical is
`intersectionIn N U w⁻¹`.

`intersectionInAmbient` merely reassociates the subtypes to the published
ambient intersection. `intersectionToSecond` sends an element `m` to
`w m w⁻¹` in the second subgroup. Their group laws are proved.
`intersectionEquiv` composes these subtype identifications with the published
ambient conjugation equivalence. Its forward map is `m ↦ w m w⁻¹` and
its inverse is `n ↦ w⁻¹ n w`; both value formulas are proved.
`intersectionEquivContinuous` proves that this is also an isomorphism of
topological groups for the induced subgroup topologies. Consequently the
representation transport in the source will use its inverse in the action.
No representation transport functor is duplicated in this module.

Conjugation preserves closedness. An intersection in `M` is closed in `M`
whenever the second subgroup is closed in the ambient group. These facts are
proved by taking preimages under the continuous conjugation maps.

## The six conditions and the two characters

`IsDecomposable H M U` is the literal set equality

`H ∩ (M U) = (H ∩ M)(H ∩ U)`.

Here the products are pointwise products of subsets, not subgroup joins.
The equivalent elementwise existence of factors in the two intersections is
proved. This definition does not assume uniqueness of decomposition, that the
product is a subgroup, or the existence of a Levi decomposition.
`SixDecomposable P M U Q N V w` is the conjunction of the three
decomposability conditions for `w(P), w(M), w(U)` relative to `(N,V)`
and the three conditions for `w⁻¹(Q), w⁻¹(N), w⁻¹(V)` relative to `(M,U)`.
These are the actual six hypotheses of section 5.1(4), not theorem conclusions
inserted as structure fields.

`intersectionCharacter M K w chi` is `chi` composed with
`intersectionToSecond M K w`. With `K=V` it gives the character `psi'`
on the source radical. With arguments `N,U,w⁻¹,theta` it gives `theta'`
on the target radical. Local constancy is proved from local constancy of the
original character and continuity of the constructed homomorphism.

`CharactersCompatible U V w theta psi` says that `w(theta)` and `psi`
agree on the actual subgroup `w(U) ∩ V`. It compares homomorphisms on
`intersectionIn V U w⁻¹`, namely
`v ↦ theta(w⁻¹ v w)` and `v ↦ psi(v)`. Its equivalence with pointwise
agreement is proved. Its failure is the zero-piece branch in the later
orbit-functor construction; no zero functor is constructed or asserted here.

## Source and remaining obligations

Original source: I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977), section 5.1,
printed pages 459–460 (PDF pages 20–21), with the inverse-conjugation
representation convention from section 1.7, printed page 443 (PDF page 4).
The retained original sections 1.7–1.9 and 5.1–5.3 were read.
Literature ID: `bernstein-zelevinsky-1977-induced-i`.
SHA-256: `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

The subtype identifications, explicit elementwise predicates, continuity proofs
and arbitrary-group formulation are internal constructions implementing the
source's actual intersections. The source does not claim these under the same
names. The proofs use subgroup inverse images, the existing ambient conjugation
equivalence, group cancellation, set-product membership and continuity of
multiplication.

Closed semidirect triple data, normalized induction and localization, the
normalizer Haar modulus, the two correction characters, normalized orbit
functors, and the ordered filtration theorem are separate units. This module
does not assume any of their theorem assertions and does not discharge the
general geometric lemma.

Author: Worker 14.
