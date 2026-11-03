# One affine finite-type model containing the trivial cocycle

`Langlands.GroupScheme.AutomorphicAction.AffineFiniteTypeCocycleModelStatement.{u}`
is an unproved proposition definition, uniform in the universe `u` and in an
arbitrary field `k`. For affine group schemes `H` and `G` locally of finite
type over `k`, and any actual automorphic action `a` of `H` on `G`, it asks
for an `a.CocycleModel` whose structure morphism is affine and locally of
finite type. Affineness makes the scheme quasi-compact, so this is an affine
scheme of finite type. Neither group is required to be smooth or connected.

The published `CocycleModel` includes a universal actual cocycle, injectivity
of the resulting family on every test scheme, an actual compatible
conjugation action of `G`, and a base section restricting to the trivial
cocycle. Thus the requested model contains the trivial cocycle and its
whole conjugation orbit as a represented subfunctor. Tests may be nonreduced
or non-quasi-compact.

This is a derived, weaker consequence of Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Lemma A.8.13 and its
proof, printed pp.553–554 (PDF pp.579–580). The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The source constructs conjugation-stable affine finite-type subfunctors of
the group-section functor of `G ⋊ H → H` and chooses a stage containing
the canonical section. In cocycle coordinates that section is trivial.
Its universal family and equivariance give the requested data. The
all-test version requires extending the affine-test construction by
scheme gluing; that comparison remains part of the proof obligation.

The proposition asks for one such model. It asserts neither
representability of the full cocycle functor nor that each family on an
arbitrary non-quasi-compact test scheme factors through one member of a
directed system. It supplies no smoothness of the action relation, affine
orbit theorem, or reductivity conclusion.
