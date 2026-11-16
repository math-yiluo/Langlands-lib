# Finite ordinary refinements on compact objects admitting action lifts

This internal specialization supplies a concrete finite-refinement input for
the general finite-cover coefficient-lifting construction. It uses the finite
equivariant refinement instance already present in the analytic comparison
statement.

`CompactLiftBasis ρ` is the subtype of ordinary quasi-étale site objects `U`
whose underlying analytic space is compact and Hausdorff and for which
`ActionLift ρ U.hom` is nonempty. Its elements retain existence of a lift as a
proposition; no lift is chosen in the indexing type.
`compactLiftBasisObject ρ` sends such an index to its ordinary site object.
The word basis here denotes this specified family of test objects. No
generation result on all objects of the site is asserted.

`compactLiftBasisIdentity` places the identity object of `X` in this family
when `X` is compact and Hausdorff and the action is continuous. It uses the
previously proved `identityActionLift`, which restricts the original action
to the whole open subgroup.

`hasFiniteBasisCoverRefinements_compactLiftBasis` assumes a topological group
and the `HasFiniteEquivariantRefinements` instance for `compactLiftSystem ρ`
and the twisted quasi-étale topology. Given a covering sieve on a member of
the family, it chooses an existing lift of that object. Its local action is
admissible. The published `nonempty_commonSubgroupRefinement` then supplies a
finite ordinary covering family in the given sieve, with compact sources and
actual source lifts. Each source therefore defines another index of
`CompactLiftBasis ρ`. The covering family and its sieve memberships give
exactly `HasFiniteBasisCoverRefinements` for the ordinary quasi-étale
topology and this family.

The refinement theorem needs neither compactness of `X` nor continuity of its
full action; these conditions are used only to place the identity in the
family. No smallness hypothesis on the group or choice of module coefficients
is needed in this construction. The base field is complete, normed and
ultrametric, with the analytic-space universes retained.

The proof is derived from the published common-subgroup refinement
construction, which translates and untwists the given finite equivariant
refinements. It does not prove that every compact quasi-étale object has an
action lift. It does not establish finite presentations of nerve terms,
augmented Čech exactness, coefficient acyclicity, or the analytic comparison
theorem.
