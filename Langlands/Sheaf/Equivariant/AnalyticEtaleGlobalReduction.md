# Analytic étale global comparison from injective acyclicity

Author: Worker 284.

This internal derived construction specializes
`ExactBaseChange.isIso_baseChangeNatTrans_of_injective_acyclic` to the
published analytic étale global comparison. It introduces no geometric
assumptions implicitly and does not prove the compact comparison statement.

The parameters are a complete ultrametric normed field `K`, the existing analytic
space `X`, a topological group `G` small in the module universe, its action `ρ`,
the admissible-refinement instance for the distinguished lift system, and a
commutative ring `R`. No compactness or continuity hypothesis is needed for this
conditional reduction.

`isIso_etaleComparison_of_injective_acyclic` assumes that the natural
transformation `etaleGlobalInclusion ρ R` is invertible. Its second premise
requires, for every injective étale `G`-sheaf `I` and every natural number `r`,
vanishing of `H^(r+1)(X, b*I)`, using exactly the published `etaleCohomology`
and `etaleGSheafRestriction` functors.

The proof supplies the established sheafification and enough-injectives
instances. Smooth global sections and ordinary global sections are additive and
left exact. Restriction is additive and preserves finite limits and finite
colimits, hence homology. Forgetting a smooth representation to its underlying
module is exact. The generic criterion therefore applies to the square with
vertical functors the smooth and ordinary global sections, horizontal functors
restriction and the smooth forgetful functor, and degree-zero transformation
`etaleGlobalInclusion`. By definition its derived base-change transformation is
the existing `etaleComparison`, with the same direction and naturality.

`etaleComparisonIsoOfInjectiveAcyclic` packages that transformation as a natural
isomorphism in every degree. Its forward map is `etaleComparison` itself.
Neither input premise is proved here; applying this construction to the compact
comparison theorem still requires independent geometric and acyclicity proofs.
