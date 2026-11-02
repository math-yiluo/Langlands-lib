# The actual torsion closure as an abelian scheme

`Langlands.AbelianScheme.Tate.twoPowerTorsionClosureAbelianScheme_exists`
proves `TwoPowerTorsionClosureAbelianSchemeStatement.{u}`.
For every algebraically closed characteristic-zero field and every actual
abelian scheme `A` over it, the theorem produces an actual abelian scheme
`B` and a homomorphism `B ⟶ A` which is a closed immersion with image the
Zariski closure of the actual geometric two-power torsion locus.

The proof takes the smooth proper commutative group scheme `G` and its
closed immersion from `twoPowerTorsionClosureGroupScheme_exists`.
The published connectedness theorem makes its image connected. The closed
immersion induces the topology on `G`; pulling connectedness back along
this embedding gives `ConnectedSpace G.X.left`. Nonemptiness is recovered
explicitly from a point in the image. Smoothness supplies local finite type,
and `Langlands.AlgebraicGeometry.algClosedConnected` supplies geometric
connectedness of the structure morphism.

The abelian scheme `B` then uses the same underlying commutative group scheme
`G`, with these smoothness, properness, and geometric connectedness instances.
Its map to `A` is the same group-scheme homomorphism, so the closed immersion
and exact range equality transfer directly.

This is an internal assembly of the geometric closure results. The characteristic
zero hypothesis is used by the connectedness theorem. No equality of dimensions,
numerical torsion formula, or density conclusion is proved here.
