# Transport between actual geometric intersections

This internal construction compares the actual subgroup conventions already
published in `Geometric.GeneralIntersections` and
`Aubert.General.GeometricK0Target`. It applies to arbitrary groups; the continuous
equivalences use the induced subgroup topologies, and conjugation continuity
additionally requires a topological group. The acting group and representation
carrier have independent universes.

For subgroups `A`, `B` and an element `n`, the source is
`B ∩ n⁻¹ A n` and the target is `A ∩ n B n⁻¹`. The membership lemmas
identify the map-defined subgroups with their inverse-image descriptions.
`geometricSourceIntersection_eq_intersectionSource` and its target counterpart
identify the published ambient subgroups. The two
`intersectionIn_*_subgroupOf` equalities identify the corresponding subgroups
inside `B` and `A` with the literal `subgroupOf` restrictions. In the target
equality the BZ representative is inverted.

`geometricSourceIntersectionEquiv` and
`geometricTargetIntersectionEquiv` reassociate the two nested subgroup
subtypes with the ambient source and target. Both maps preserve the underlying
ambient element and are continuous in both directions. They choose no
structural identification or normalizer lift.

`geometricIntersection_conjugationEquiv` compares these equivalences with the
published forward BZ conjugation and the actual Aubert inverse conjugation.
Starting in the ambient target, the composite passes to the target subgroup
inside `A`, applies the inverse BZ conjugation, and returns to the ambient
source. It equals the published `conjugationEquiv` and sends `x` to
`n⁻¹ x n`. `geometricIntersection_transport_apply` gives the resulting
representation action. `geometricIntersectionTransportIso` proves the natural
comparison with the actual `conjugationFunctor`: its components are identity
linear equivalences, and the intertwiners retain their original linear maps.
`geometricIntersection_conjugationK0` proves equality of the three continuous
equivalence pullbacks with the actual `conjugationK0` on the full exact
finite-length Grothendieck groups.

The proofs use `Subgroup.mem_map_equiv`, subtype extensionality, the published
`Geometric.General.intersectionEquiv_symm_apply`, and continuity of the subtype
inclusions. The representation comparison uses the preceding equality of
continuous group equivalences. The K0 comparison uses the published
`SmoothRep.FiniteLengthGrothendieckGroup.pullback_trans`; it adds no new
additivity statement or class-equation premise.

This is a derived interface comparison, not a new translation of a source
theorem. The source conventions are documented by the two imported pairs:
BZ77 section 5.1 uses the orbit `P_J n⁻¹ P_I`, and the Aubert target transports
a source representation by the action `x ↦ σ(n⁻¹ x n)`.
No original literature is needed to prove the equality of the existing
definitions. No statement is made about geometric filtrations, graded
integrals, the two Haar correction cancellations, normalized Jacquet or
induction comparison, actual orbit indexing, quotient compactness, or standard
Levi conjugation and lift independence. These remain separate obligations for
the full rational-point geometric K0 expansion.

Proof-body dependencies are elementary group/subtype topology,
the existing intersection-conjugation value formula, smooth pullback, and exact
K0 pullback composition. In particular, `pullback_trans` uses
`pullbackFunctor_preservesFiniteLength`, whose proof applies
`FiniteLengthAssembly.finiteLength_comp_surjective_iff`. That theorem reduces to
`length_comp_surjective`, the group-algebra/subrepresentation order
identifications and
`CuspidalSupport.JacquetLength.compSubrepresentationOrderIso` for a surjective
homomorphism. This is an elementary order-isomorphism argument for arbitrary
representations. Short-exact preservation retains the underlying linear maps;
equality of classes under an intertwining equivalence is a defining K0 relation.
No geometric lemma, adjointness, cuspidal-support existence or uniqueness,
character-independence or Langlands-classification theorem is used in this
chain. The file containing the algebraic finite-length transport has broader
GL finite-length and cuspidal-support imports, and
`CompactCoefficient.GroupTransport` has cuspidal-support imports as well.
Those imported-module dependencies are distinct from the declaration-level
proof dependencies just listed. The other imported modules supply the existing
actual normalized functor/K0 definitions; their mere import is not an
application of their representation-theoretic results.

Author: Worker 184.
