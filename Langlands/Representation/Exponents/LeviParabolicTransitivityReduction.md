# Reduction of represented transitivity to nested radical identities

Authors: Worker 1373, with Worker 1754 contributing the agreed structural interface. Module `Langlands.Representation.Exponents.LeviParabolicTransitivityReduction`, namespace `Langlands.Aubert.General.RepresentedParabolic`.

The construction `leviParabolicTransitivityComparisons` returns a pair of actual natural isomorphisms between the published represented-Levi induction and Jacquet functors. Its supporting theorem `leviParabolicTransitivity_of_radical_decomposition` asserts the conjunction of their nonemptiness. These are internal derived adapters for the proof of Renard 2026 VI.1.4, not proofs of the unconditional published `LeviParabolicTransitivityStatement`.

The source context is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.1.4, printed pp.136–137/PDF pp.142–143, with the coinvariant construction in III.2.9, printed p.78/PDF p.84. Registered source: `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The implementation reuses the Library's generic induction, coinvariant and Haar-modulus comparisons, rather than Renard's deduction of induction by uniqueness of adjoints.

## Scope

The ambient field, topology, local-field hypotheses, arbitrary field universe `u`, representation-carrier universe `v`, three actual rational parabolic triples, ambient local compactness and nonarchimedean-group assumptions are those of the target. The helper explicitly assumes the affine structure morphism of `G`, which connected reductivity supplies in the target. It takes the same rational-point containment, same composite Levi embedding and inner-parabolic image equality as the target.

There are exactly two additional structural hypotheses:

- The image of `nL ≫ pL ≫ l ≫ q` is the intersection of the images of `l ≫ q` and `n ≫ p` in `G(k)`.
- As subsets of `G(k)`, the image of `n ≫ p` is the product of that intersection and the image of `uQ ≫ q`.

No representation finiteness, admissibility, standardness, quotient compactness, chosen cocharacter or additional topological premise is used. Local compactness and the nonarchimedean-group structure of `L(k)` are derived through the canonical `leviPointsEquiv`; the topology on each Levi is the published canonical topology. The induction isomorphism has output carrier universe `max u v`, with the outer induction evaluated at that universe. Jacquet restriction preserves `v`.

The two structural hypotheses must still be proved from the target's existing hypotheses before the unconditional theorem can be discharged. The parabolic product `P = P_L U` is not an extra premise of this adapter.

## Implemented construction

The canonical outer Levi homeomorphism identifies membership in the inner parabolic, Levi and radical point images with membership in the literal subgroups `P.subgroupOf L`, `M.subgroupOf L` and `N.subgroupOf L` of the outer Levi image. Injectivity of that homeomorphism reflects point-image membership. The inner Levi comparison uses the equality of composite morphisms. The other two membership comparisons use the parabolic-image and radical-image identities respectively.

`GroupTransport.semidirectDecomposition` then transports the given inner semidirect decomposition into these literal subgroups. The published continuous represented Levi projection supplies outer projection continuity. `RationalPointFamily.reductiveRationalPoint_secondCountable` supplies ambient second countability from connected reductivity and the local field. `LeviRadicalCompactSubgroups` supplies compact-subgroup limits for both ambient radicals, their unimodularity, and, by restriction to the closed outer Levi, the compact-subgroup limit needed for the inner Jacquet functor.

`NestedParabolic.halfCharacterProduct` derives the positive half-modulus product from the actual radical product. `NestedInduction.iso` uses this identity to compare ambient normalized induction with induction in stages. `NestedParabolic.jacquetIso` derives the normalization identity for coinvariants and supplies the Jacquet comparison. Thus the adapter assumes no modulus identity.

`GroupTransport.inductionIso` and `GroupTransport.jacquetIso` transport the inner generic functors to the actual group `L(k)`. The composite Levi embedding gives the equality between the resulting coefficient-group identifications and the canonical inner Levi-point homeomorphism. Explicit natural isomorphisms with identity linear maps cancel the resulting pullbacks. After reassociation, the resulting functors are precisely the published `leviInductionFunctor` and `leviJacquetFunctor` of the target, for every `v`. The exported definition chooses the two natural isomorphisms supplied by the supporting nonemptiness theorem.

## Verification boundary

The module compiles with no diagnostics. Declaration inspection of `leviParabolicTransitivityComparisons` reports a definition with universe parameters `u`, `v`, returning a product of natural-isomorphism types. Only the standard assumptions `propext`, `Classical.choice` and `Quot.sound` occur. This construction does not assert the two structural identities and does not by itself establish the task's unconditional target.
