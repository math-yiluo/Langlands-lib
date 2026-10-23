# Pullback of rigidified families along homomorphisms

For abelian schemes `A` and `B` over an arbitrary scheme `S` and a
homomorphism `f : A ⟶ B`, this module constructs actual pullback of
rigidified line bundles along `T ×_S A → T ×_S B` for every parameter
scheme `T` over `S`.

`unitSection_hom` obtains preservation of the unit section from the
group homomorphism on points over `S`. `homFamilySpaceMap f` is the
natural transformation between the two relative total-space functors:
its component is the fibre-product lift of the first projection and the
second projection followed by the underlying morphism of `f`.
The fibre-product projection formulas prove naturality, preservation
of the relative unit section, and the identity and composition formulas.

`homFamilyPullback f T` applies the existing rigidified-line-bundle
pullback functor to this map, the identity of `T`, and the proved
commuting square of unit sections. Its underlying module sheaf is
the actual module pullback. In particular, the rigidification is
transported by the existing canonical structure-sheaf comparison;
it is not chosen independently. `homClassesPullback f T` descends
this functor to isomorphism classes using its map on isomorphisms.

Under the explicit `RigidifiedModule.PullbackCoherenceStatement`
hypothesis, `homFamilyPullbackId` and `homFamilyPullbackComp` lift
the established identity and composition comparisons to these
families. The two corresponding class equalities follow by quotient
induction from those rigidified isomorphisms. The composition order
is contravariant: pullback along `f ≫ g` equals pullback along `g`
followed by pullback along `f`.

## Provenance and scope

This is derived infrastructure for the dual-homomorphism construction
required by parent-task item 4. The registered source is Edixhoven,
van der Geer and Moonen, *Abelian Varieties*, preliminary draft,
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter VI paragraph (6.2), printed p.88 (PDF p.92), gives rigidified
line bundles and their pullback formulation. The present construction
specializes ordinary rigidified pullback to the commuting unit-section
square furnished by an actual abelian-scheme homomorphism.

No field or noetherian hypothesis is used. This module does not
assert preservation of the geometric Picard-zero condition, construct
a morphism of representing dual schemes, supply a tensor group law,
or assert additivity in `f`. Those are subsequent constructions and
proof obligations.
