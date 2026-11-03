# Semigroup intersection along equivariant retractions

This is a derived, formal consequence of retractions and functoriality. It supplies
the final direct-factor step in a possible proof of the normal-subgroup
intersection comparison. It proves no existence theorem for a retraction.

`AutomorphicAction.IsEquivariantRetraction b c j r` is a proposition about group
schemes over an arbitrary base scheme. It says that `j : H ⟶ G` and `r : G ⟶ H`
are equivariant on every test scheme, and `j ≫ r = 𝟙 H`. No condition in this
definition only tests points over fields. In particular, the retraction identity
and action compatibility retain points over nonreduced schemes.

For any subgroup functors `F` of `G` and `E` of `H`, suppose their images under
`r` and `j` are respectively contained in `E` and `F`. The theorem
`SubgroupFunctor.comap_eq_of_retraction` proves `F.comap j = E`. To prove the
nontrivial containment, take `x` with `j(x)` in `F` and apply `r`; the retraction
identity gives `r(j(x)) = x`. The reverse containment is the assumed preservation
by `j`. The companion `map_eq_of_retraction` proves `F.map r = E`, using `j(x)`
as a preimage of each `x` in `E`. Both equalities hold as subgroup functors.

For smooth affine groups over an arbitrary field and an action by a split torus,
`RelativeRoot.semigroup_comap_eq_of_equivariantRetraction` applies this argument
to the actual semigroup subgroup functors. It retains the independent global
`SemigroupFunctorialityStatement` as an explicit premise. That premise ensures
preservation by both equivariant maps. There is no restriction on the additive
semigroup, so it may contain zero; no connectedness assumption is imposed on the
ambient group or the retract. The companion
`semigroup_map_eq_of_equivariantRetraction` gives the image equality, which here
also expresses surjectivity on every original test because a section is supplied.

These formal deductions do not establish the general functoriality theorem,
existence of semigroup representatives, or a retraction for a normal subgroup.
They do not prove the full `SemigroupComparisonStatement`. In particular, using
the first theorem in the normal case still requires the geometric reduction to
an equivariant retract and a proof of general functoriality. The argument uses
only the published actual subgroup-functor image and inverse-image definitions,
and the published functoriality proposition; it invokes no external source
result as a theorem.
