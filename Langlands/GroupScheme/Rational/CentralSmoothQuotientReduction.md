# Central smooth quotients from explicit structural inputs

This derived module combines the actual homogeneous quotient and action
constructions with three explicit proposition hypotheses:
`UnipotentAffineOrbitClosedStatement`, `UnipotentFieldExtensionStatement`,
and `UnipotentClosedSubgroupStatement`. It does not prove these hypotheses.
The base field is arbitrary and belongs to any universe `u`.

`Chevalley.unipotentAffineQuotientOfStructuralStatements` constructs an actual
`AffineHomogeneousQuotient i` for a smooth closed subgroup `i : H ⟶ G` of
a smooth affine unipotent group scheme over `Spec k`. Smoothness supplies
the local finite type hypotheses. The closed immersion and the affine
structural morphism of `G` make `H` affine. The closed-subgroup hypothesis
then gives unipotence of `H`. Applying the field-extension hypothesis to
both groups supplies unipotence after base change to `AlgebraicClosure k`,
which lies in the same universe. The previously constructed
`unipotentAffineQuotientOfFieldExtension` now supplies the affine quotient
over the original field. Neither normality nor connectedness is needed
for this construction.

`RelativeRoot.centralSmoothQuotient_of_structuralStatements` proves the
exact existing `CentralSmoothQuotientStatement` under these three inputs.
Its data include a smooth connected affine unipotent `G`, a smooth
connected central closed subgroup `Z`, a split torus with actions on both
groups, and an equivariant inclusion. The theorem retains the published
scope, including arbitrary fields, arbitrary actions and every supplied
pair of relative dimensions `d, n` with `0 < n`.

The proof uses the published `IsCentral.range_isNormal` to obtain
normality of the actual subgroup functor, and the published
`AutomorphicAction.IsEquivariant.isStable_range` to obtain its stability
on every test scheme. It applies
`HomogeneousQuotient.exists_action_relativeDimension` to the affine
quotient just constructed. The resulting group scheme `Q`, homomorphism
`q`, descended action and natural number `m` have precisely the target
properties: `Q` is affine, smooth, connected and unipotent; `q` is an
actual fppf quotient with kernel functor `SubgroupFunctor.range z`; `q`
is smooth of relative dimension `n`; `Q` is smooth of relative dimension
`m`; `d = n + m` and `m < d`; and the quotient action intertwines with
the original action on every relative test scheme.

The provenance is internal and derived. No new source assertion is
introduced: the construction applies the prior field-descent quotient
and normal quotient adapters, and the final theorem specializes them to
the exact central target. It leaves all three structural inputs, central
stable vector-subgroup existence, and the full
`SemigroupOrderedProductStatement` open.
