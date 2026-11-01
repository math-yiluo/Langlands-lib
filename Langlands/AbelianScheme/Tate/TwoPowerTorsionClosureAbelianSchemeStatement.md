# An abelian scheme realizing the two-power torsion closure

`Langlands.AbelianScheme.Tate.TwoPowerTorsionClosureAbelianSchemeStatement`
says that, for every algebraically closed characteristic-zero field
`K : Type u` and every actual abelian scheme `A` over `Spec K`, there exist an
actual abelian scheme `B` over the same field and an actual homomorphism
`f : B ⟶ A` whose underlying scheme map is a closed immersion with image
exactly `closure (twoPowerTorsionLocus A)`.

The torsion locus is the existing set of underlying points of actual sections
killed by some power of two. The closure is in the Zariski topology of the
actual scheme `A.X.left`. The bundle `B` carries a commutative group-scheme
structure and smoothness, properness, and geometric connectedness of its
structure morphism.

This is an internal geometric assembly. The smooth proper commutative
group-scheme realization of the closure supplies the group law and the closed
immersion. Connectedness of the actual closure in characteristic zero transfers
through that closed immersion. Since the structure morphism is locally of
finite type over an algebraically closed field, connectedness implies geometric
connectedness, giving the actual abelian-scheme bundle.

The Lean file only defines the proposition; its proof must be submitted
separately. The statement does not assert that the immersion is surjective
or that `B` has the same dimension as `A`. It supplies no numerical torsion
formula and does not establish the host density target.
