# Central smooth quotients from explicit structural inputs

Author: Worker 362.

This derived module combines the actual homogeneous quotient and action
constructions. Its original adapters have three explicit proposition hypotheses:
`UnipotentAffineOrbitClosedStatement`, `UnipotentFieldExtensionStatement`,
and `UnipotentClosedSubgroupStatement`. The two-input adapters described below
discharge field-extension unipotence using its published proof. Closed-orbit
and closed-subgroup unipotence remain explicit inputs. The base field is
arbitrary and belongs to any universe `u`.

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

`Chevalley.unipotentAffineQuotientOfClosedOrbitAndSubgroup` takes only
`UnipotentAffineOrbitClosedStatement` and `UnipotentClosedSubgroupStatement`,
followed by exactly the same fields, groups, inclusion and geometric
hypotheses as the original constructor. It supplies
`Langlands.GroupScheme.unipotentFieldExtensionStatement` from the published
[`UnipotentFieldExtensionProof`](../Reductive/UnipotentFieldExtensionProof.md)
to `unipotentAffineQuotientOfStructuralStatements`. Thus it constructs an
actual `AffineHomogeneousQuotient i` over any field without a field-extension
premise. In particular, it imposes no perfectness, characteristic or
separability restriction on the base field.

`RelativeRoot.centralSmoothQuotient_of_closedOrbit_and_subgroup` supplies
the same published theorem to
`centralSmoothQuotient_of_structuralStatements`. Its conclusion is the exact
`CentralSmoothQuotientStatement.{u}` under only the two remaining structural
propositions. It consequently retains every central quotient property
listed above, including the actual fppf kernel, the action on all test
schemes and the strict dimension decrease.

The provenance is internal and derived. No new source assertion is
introduced: the constructions apply the prior field-descent quotient,
normal quotient and field-extension unipotence results by their Lean
names. This module does not discharge either remaining structural input,
central stable vector-subgroup existence, or the full
`SemigroupOrderedProductStatement`.
