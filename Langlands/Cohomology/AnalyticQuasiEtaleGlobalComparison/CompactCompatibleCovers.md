# Cofinal compact covers with compatible local actions

This internal construction retains the action data of finite ordinary
refinements instead of retaining only existence of lifts on their source
objects. It specializes the published common-subgroup refinement theorem
using the finite equivariant refinement instance already assumed by the
analytic comparison statement.

`CompactCompatibleCover ρ i` consists of a finite ordinary quasi-étale
cover of `compactLiftBasisObject ρ i` by members of the compact-with-lifts
family, an actual target lift, an actual lift on each source, and one open
subgroup contained in all their acting subgroups. On that subgroup every
covering arrow intertwines the source and target actions. The displayed
equivariance equality is in the twisted-over category under the ordinary
inclusion, with the same group element on each side. No independently
chosen lift for a source index is used.

`compactCompatibleCoverOfRefinement` preserves these data from an actual
`CommonSubgroupRefinement`. The source objects lie in the specified family
because their compactness and lifts are stored in that refinement.

`exists_compactCompatibleCover_refinement` fixes any existing lift on the
target and any covering sieve. That lift is admissible because the target
is compact. The common-subgroup refinement theorem supplies a compatible
cover whose arrows belong to the sieve and whose target lift equals the
prescribed lift. Thus these covers refine all covering sieves on the test
family; no compatibility of arbitrary arrows with arbitrary lifts is
asserted.

`exists_compactCompatibleCover_cech_lift` proves local coefficient lifting
using these compatible covers. For a short exact sequence of ordinary module
sheaves, the final map is epimorphic, hence locally surjective under the
explicit `WEqualsLocallyBijective` hypothesis. The image sieve of a map
from a free representable sheaf is covering. Refine it with the preceding
theorem. The stored local section lifts assemble into a map from the finite
coproduct of free source sheaves. Composing with the degree-zero finite
Čech presentation produces a lift along the actual free Čech augmentation;
the augmentation comparison proves the required equality. The target lift
is still the one prescribed by the caller.

The analytic field is complete, normed and ultrametric, and the analytic
space universes remain independent. The construction of the cover uses a
group and topology; the refinement and lifting theorems additionally use
the topological group and finite equivariant refinement instances.
Coefficient lifting assumes local smallness in the module universe and
module sheafification. Compactness of the base space and continuity of
its full action are not required here; they place its identity in the
test family in `CompactLiftBasis`.

The derivation is internal, from the published common-subgroup refinement
construction and the free-representable coefficient-lifting and degree-zero
Čech comparison lemmas. This module does not construct higher nerve
products or presentations, prove augmented Čech exactness or coefficient
Hom acyclicity, or prove the analytic comparison theorem.
