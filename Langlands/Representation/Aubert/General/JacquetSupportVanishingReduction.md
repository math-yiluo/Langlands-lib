# Full smooth support vanishing from common-constituent presentations

This internal conditional construction supplies an associated-subset witness
from nonzero actual Jacquet restriction, and thereby proves the generic
`Langlands.Aubert.General.SupportCategoryJacquetVanishingTarget` from six
explicit inputs. It applies to all smooth objects in the support category,
with independent index, group and carrier universe parameters `uI`, `uG`,
`uV`, and carriers in `max uG uV`. It requires neither finite length nor
admissibility and places no finiteness restriction on the index type.

The construction
`Langlands.Aubert.General.associatedSubsetOfNonzeroJacquet` takes `I`, `K`,
a smooth `E` in `Alg({I})` and nontriviality of its Jacquet module at `K`,
in addition to the six inputs below. Its value is a pair `(J, p)` together
with `J ⊆ K`, association `I → J` represented by `p`, and the exact
membership equivalence `x ∈ M_J ↔ p⁻¹ * x * p ∈ M_I`.
The resulting theorem is
`Langlands.Aubert.General.supportCategoryJacquetVanishing_of_inducedCuspidalPresentations`.
Its families, actual normalized functors, inside-Levi cuspidality predicate,
support category and vanishing conclusion are exactly those of
[SupportCategoryStatements](SupportCategoryStatements.md) and
[SupportCategory](SupportCategory.md).

## Explicit inputs

1. For every standard index `K`, the actual left quotient `P_K \ G` is compact.
2. Every actual unipotent subgroup `U_K` has trivial conjugation Haar modulus,
   as expressed by `IsUnimodularModulus (U K) (hU K)`.
3. If `τ` is an irreducible smooth representation of `M_K` and `π` is an
   irreducible subquotient of its actual normalized induction to `G`, then
   some `J ⊆ K` and an irreducible, actually Levi-cuspidal `σ` of `M_J`
   give an actual subquotient presentation `π ≤ i_J(σ)`. This is a premise,
   not a result of this module.
4. The entire `CuspidalSupportAssociationTarget`, including the actual
   conjugation membership certificate and the isomorphism of cuspidal data.
5. Transport of the precise `IsLeviCuspidal` predicate along the specified
   actual association representative and its membership certificate.
6. Composition of association representatives: first `n : I → L`, then
   `m : L → J`, is represented by the literal element `m * n`.

These inputs are universally quantified over the same families as the generic
target. In the intended rational-point application, inside-Levi cuspidal-series
existence and actual induction in stages provide a route to input 3; this module
does not establish those existence statements. The published adapter in
[RationalSupportInduction](RationalSupportInduction.md) transports an already
supplied inside-Levi induction presentation to the required ambient one.

## Implemented proof

Fix `I`, `K`, the target's literal absence-of-associated-subset hypothesis,
and any smooth `E` in `Alg({I})`. Suppose its actual normalized Jacquet module
at `K` is nontrivial. The published construction
`JacquetCommonConstituent.of_nontrivial_jacquet`, using inputs 1 and 2,
gives irreducible smooth representations `τ_K` of `M_K` and `π` of `G`,
with `π` an actual subquotient of both `E` and `i_K(τ_K)`. This step works
for arbitrary smooth `E`; see
[JacquetCommonConstituent](JacquetCommonConstituent.md).

Input 3 presents this same `π` inside `i_J(τ)` for an irreducible cuspidal
`τ` and some `J ⊆ K`. Support-category membership of `E` presents `π` inside
`i_L(Ad(n)(σ))`, where `n` associates `I` to `L` and `σ` is irreducible
cuspidal on `M_I`. Irreducibility is preserved by the actual continuous
conjugation equivalence; input 5 gives cuspidality of `Ad(n)(σ)`.

Input 4 applied to the two actual presentations returns an association
`m : L → J` with the precise inverse-conjugation membership equivalence.
Input 6 gives association `I → J` through `m * n`. The published
`conjugationMembership_mul` from
[ConjugationComposition](ConjugationComposition.md) composes the two
membership certificates at this same element. Classical choice turns the
existence of this certified pair into the value of
`associatedSubsetOfNonzeroJacquet`.

The vanishing theorem supposes that the Jacquet module is nontrivial, applies
the construction, and contradicts the target hypothesis for its `J ⊆ K`.
The Jacquet module of `E` is therefore subsingleton.
The supplied isomorphism of cuspidal data is stronger than this contradiction
needs, and is not used.

## Provenance and scope

This is derived internal content obtained by composing the cited published
constructions and the explicit hypotheses. It makes no new direct literature
assertion. The proof uses actual representations and actual subquotients.
It does not pass through a Grothendieck group, claim a nonzero Jacquet module
for the common irreducible constituent, or lift vanishing from simple objects
by exactness alone.

This supporting theorem does not prove
`RationalSupportCategoryJacquetVanishingStatement`. Compactness, unimodularity,
the induced-constituent cuspidal presentations, association, cuspidality
transport and composition all remain explicit in its type. In particular,
the module discharges neither rational parabolic quotient compactness,
inside-Levi cuspidal-series existence nor cuspidal-support association.
