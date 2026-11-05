# Functoriality of rational identity-component quotients

This internal derived construction makes the published ordinary quotient
`RationalComponentQuotient H = H(k) / H⁰(k)` functorial under actual
group-scheme homomorphisms. The field `k`, schemes and tests share an arbitrary
universe `u`. Every source, target and intermediate group scheme is smooth and
affine over `k`. There is no characteristic, perfection, connectedness or
reductivity hypothesis.

## Construction and intrinsic laws

The published `IdentityComponent.map f` restricts an actual homomorphism
`f : H → H'` to the actual identity components. Its inclusion equation proves
`comp_mem_rationalIdentitySubgroup`: if a rational section factors through
`H⁰`, its composite with `f` factors through `H'⁰`. The witness is its section
of `H⁰` followed by `map f`.

`rationalComponentMap f` applies the existing `rationalComponentLift` to
postcomposition on rational sections followed by the target quotient
projection. The subgroup preservation just proved and the published exact
kernel of that projection supply the lift's kernel hypothesis. The actual
postcomposition homomorphism is the identity-test specialization of the
published `GroupScheme.pointsMap`.

`rationalComponentMap_projection` computes the induced homomorphism on every
projected rational point: the image of the class of `x` is the class of
`x ≫ f`. Surjectivity of the source projection gives
`rationalComponentHom_ext`, an extensionality principle for homomorphisms out
of the quotient, with any target group in any universe. Checking projected
sections with this principle proves `rationalComponentMap_id` and
`rationalComponentMap_comp`.

`rationalComponentEmbedding_naturality` compares these homomorphisms with
the published injections into the connected components of the underlying
schemes. For every quotient element `c`, embedding its image under
`rationalComponentMap f` equals applying the continuous scheme map of `f`
on connected components to the embedding of `c`. Surjectivity reduces this
equation to the defining representative computations.

`rationalComponentEquiv e` uses `rationalComponentMap e.hom` and
`rationalComponentMap e.inv` for an actual isomorphism `e : H ≅ H'`.
The identity and composition laws give the two inverse equations.
Its underlying homomorphism and projected-section computation are
`rationalComponentEquiv_toMonoidHom` and
`rationalComponentEquiv_projection`. Its inverse is the equivalence induced
by `e.symm`, as stated by `rationalComponentEquiv_symm`.

## Provenance and scope

The provenance is internal and derived from
`IdentityComponentRationalQuotient`, `IdentityComponent.Transport`,
`GroupScheme.pointsMap`, and Mathlib's induced maps on topological connected
components. The new maps and their laws verify the behavior of these
composed constructions. No external literature theorem is invoked.

The quotients remain ordinary quotients of rational-point groups. These maps
construct no quotient scheme or sheaf quotient and supply no comparison with
the rational points of such a quotient. The embedding targets actual scheme
connected components and is not asserted surjective. No rational-point
topology or field-extension compatibility is asserted.
