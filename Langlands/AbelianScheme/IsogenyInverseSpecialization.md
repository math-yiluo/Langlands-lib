# Conditional rational invertibility for bundled abelian schemes

Authors: Worker 131 and Worker 6.

`Langlands.AbelianScheme.IsogenyInverseStatement` is the specialization of
the published `Langlands.CommGroupScheme.IsogenyInverseStatement` to the
actual bundled abelian schemes and their published rational category.
For every scheme `S`, abelian schemes `A` and `B` over `S`, and homomorphism
`f : A ⟶ B`, it states that the following two hypotheses imply that
`(rationalization S).map f` is an isomorphism:

1. `IsIsogeny f`: its underlying scheme morphism is finite, flat, and
   surjective.
2. One nonzero integer annihilates the actual scheme kernel of
   `groupHom f`.

The second hypothesis uses the published scheme kernel and multiplication
map. In its equation, `1` denotes the zero group homomorphism in
multiplicative notation. It does not denote the categorical identity.
The integer is uniform over the whole base, not chosen separately on each
component. There are no restrictions on the base scheme. The abelian-scheme
bundle retains Basic's explicit commutativity, smoothness, properness, and
geometrically connected fibres.

The conclusion concerns the actual category `RationalCategory S` from
`Rational`: its Hom groups are `ℚ ⊗[ℤ] Hom_S(A,B)` and the canonical map
sends `f` to `1 ⊗ f`. Thus `IsIso` asserts a two-sided rational inverse.
It does not assert that this inverse is a scheme morphism.

`isogenyInverseStatement_of_commGroupScheme` proves only the implication
from the explicitly named generic inverse target to this bundled target.
Its proof applies the generic hypothesis to the underlying commutative
group schemes and unpacks the resulting inverse and its two equations.
Basic defines abelian-scheme Hom groups and composition through those
underlying objects, so the rational Hom groups, identities, and
compositions agree definitionally in both categories. Repacking the same
inverse and equations therefore proves the bundled conclusion. Worker 6
supplied this unpacking and repacking argument; Worker 131 supplied the
bundled statement and integration.

This is an internal interface specialization of the published
`IsogenyInverseStatement`, `IsogenySpecialization`, and `Rational` modules.
It adds no original literature claim. The geometric motivation and
source boundaries remain those documented in
`IsogenyInverseStatement.md`. The generic inverse theorem remains a
separate proof obligation. This file neither proves that theorem nor
asserts unrestricted rational invertibility over an arbitrary base.
