# Full smooth support vanishing on actual rational-point families

This internal adapter combines the published inside-Levi cuspidal embedding,
induction and subquotient transport, common-constituent support reduction, and
actual conjugation transport. It uses the literal rational-point group with
the canonical `pointTopology`, actual standard parabolics, Levis and radicals,
and the actual normalized smooth functors.

The field universe `u` and carrier parameter `v` are independent.
Representation carriers lie in `max (u + 1) v`, as in
`RationalSupportCategoryJacquetVanishingStatement`. The local-field, reductive,
maximal-split-torus, generic-cocharacter, standard-cocharacter and
Levi-intersection hypotheses remain explicit, as do ambient local compactness,
the nonarchimedean group structure, Hausdorffness and closedness of the standard
Levis and radicals. The support construction also retains a relative root
system, the point normalizer and centralizer comparisons and a monomorphism
instance for the torus embedding, which the maximal-split-torus hypothesis
supplies in the target.

## Remaining mathematical inputs

Three additional inputs remain explicit:

1. Compactness of every actual ambient left quotient `P_K \ G`.
2. Compactness of every literal inside-Levi left quotient
   `(P_J ∩ M_K) \ M_K`, for the fine index `J = leviIndex K I`.
3. The full `CuspidalSupportAssociationTarget` for these actual families,
   including the same-point subgroup membership certificate and isomorphism
   of the cuspidal inducing data.

The module does not prove any of these three inputs. In particular, its
conditional result is not a proof of the unconditional published rational
vanishing statement.

## Implemented constructions and proof

`exists_induced_cuspidal_presentation_of_leviCompact` starts with an irreducible
smooth representation `τ` of `M_K` and any subquotient `π` of its ambient
normalized induction. It does not require `π` to be irreducible.
The published
[`exists_cuspidal_embedding_in_levi`](RationalLeviCuspidalEmbedding.md), using
input 2, gives `I : Finset K` and irreducible cuspidal `σ` on the actual fine
Levi indexed by `J = leviIndex K I`, together with an actual embedding of `τ`
into the normalized induction of `σ` inside `M_K`.
`SmoothRep.IsSubrepresentation.isSubquotient` turns this embedding into an
actual subquotient presentation. The published
[`standardInduction_stages_subquotient_transitive_of_standardData`](RationalSupportInduction.md)
uses exact ambient induction, the normalized induction-in-stages isomorphism
and actual subquotient transitivity to place `π` in the direct ambient
induction of `σ`. `leviIndex_subset` gives `J ⊆ K`.

`rationalAssociatedSubsetOfNonzeroJacquet` takes a smooth support-category
object `E`, indices `I` and `K`, and a nontrivial actual Jacquet module at `K`.
It returns a certified pair `(J, p)` with `J ⊆ K`, actual root association
`I → J` represented by `p`, and the exact equivalence
`x ∈ M_J ↔ p⁻¹ * x * p ∈ M_I`.

It instantiates the published generic construction
[`associatedSubsetOfNonzeroJacquet`](JacquetSupportVanishingReduction.md).
Input 1 supplies ambient quotient compactness. Standard unipotent
unimodularity is discharged by the published
`standardUnipotent_isUnimodular_of_standardCocharacterStatement` in
[`RationalUnipotentRegularity`](RationalUnipotentRegularity.md). The preceding
presentation theorem discharges the induced-constituent presentation premise.
Input 3 supplies cuspidal-support association. The published
[`isLeviCuspidal_conjugation`](RationalSupportAssociationInvariance.md)
discharges transport of the exact proper-standard inside-Levi vanishing
predicate; [`rootAssociation_mul`](RootAssociationComposition.md) discharges
composition of actual representatives. The generic construction retains the
same literal product `p = m * n` in association and inverse-conjugation
membership.

`rationalSupportCategoryJacquetVanishing_of_compact_and_association` proves
the exact generic `SupportCategoryJacquetVanishingTarget` specialized to the
rational-point families under inputs 1–3. If the actual Jacquet module of
`E` were nontrivial, the certified pair above would contradict precisely the
target's absence-of-associated-subset hypothesis.

These constructions cover arbitrary smooth objects. They assume neither
finite length nor admissibility, pass through no Grothendieck group, and
make no claim that the irreducible common constituent itself has a nonzero
Jacquet module.

## Provenance

This is derived internal content, with no new direct literature assertion.
Worker 158 assembled the published generic reduction and rational induction
adapters with Worker 593's published inside-Levi embedding. The cited
published modules supply their own source correspondence and scope.
The imported target and all its dependencies remain unchanged.
