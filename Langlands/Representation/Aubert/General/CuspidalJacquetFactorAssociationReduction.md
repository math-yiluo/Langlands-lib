# Association through one common actual cuspidal Jacquet factor

Authors: Worker 55.

This internal construction compares two actual smooth data through a common
conjugate datum. Supporting conditional assembly results combine it with the
named cuspidal Jacquet-factor extraction target. This pair proves neither the
extraction theorem nor existence of a cuspidal Jacquet factor and does not prove
the closed rational-point association statement.

`conjugationDataIsoOfCommonConjugate` takes actual isomorphisms
`τ ≅ c_n₁(σ)` and `τ ≅ c_n₂(σ')`. It reverses the second using the published
`conjugationDataIsoSymm` and composes it with the first using
`conjugationDataIsoTrans`. The resulting actual smooth isomorphism is
`σ' ≅ c_(n₂⁻¹ * n₁)(σ)`. The same product supplies the actual Levi membership
equivalence, explicitly constructed by `conjugationMembership_inv` and
`conjugationMembership_mul` in its return type. The definition returns the
actual isomorphism, including its equivariant linear maps and inverse.
It requires no association relation, irreducibility or cuspidality.

`associatedData_of_common_conjugate` uses this construction to give the
existential datum comparison. The association relation is assumed to respect
inversion and products in this order, so the same element also associates the
indices. This algebraic lemma requires no irreducibility or cuspidality.

`associatedData_of_cuspidalJacquetFactor` assumes the named extraction target,
two irreducible cuspidal inducing data whose normalized inductions contain an
actual common smooth subquotient `π`, and an actual irreducible cuspidal
subquotient `τ` of one fixed normalized Jacquet module of `π`. Applying
extraction to both inducing data yields the two isomorphisms above. The
algebraic lemma then gives their actual association. This lemma does not
require `π` to be irreducible.

`cuspidalSupportAssociationTarget_of_cuspidalJacquetFactors` assumes such a
cuspidal Jacquet factor exists for every irreducible `π` and proves the existing
generic association target. Its proof chooses the factor once and uses it for
both inductions. The factor is only an actual Jacquet subquotient; no induction
realization for that factor is a premise.

The ambient-group universe and smooth-carrier universe remain independent:
the carriers have the existing size `max uG uV`. There is no finite-length,
admissibility, finite-generation or compact-limit premise in these reductions.
The subgroup families and association relation are generic, with exactly the
explicit hypotheses displayed in Lean. A rational-point application must prove
both the extraction target and factor existence under its original hypotheses,
and supply the published root-association inversion and product laws. These
conditional results do not add hypotheses to the closed published target.

The provenance is internal. The proof only applies the named extraction
proposition as a hypothesis, composes the published actual equivariant
isomorphisms, and introduces the quantifiers of the existing association target.
No new literature assertion is claimed.
