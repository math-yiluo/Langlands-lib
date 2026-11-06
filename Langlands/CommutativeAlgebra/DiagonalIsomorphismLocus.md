# Principal certificates for diagonal isomorphisms

This internal algebraic development works over an arbitrary commutative ring
`R : Type u`, with additive commutative monoids in independent universes. It
constructs scalar extension of a bialgebra map between their monoid algebras in
the canonical monoid-algebra coordinates. The map is the existing tensor
scalar-extension algebra map composed on the source with the inverse of
`AddMonoidAlgebra.scalarTensorEquiv`.

The coefficient-change map preserves group-like elements, by naturality of the
standard diagonal counit and comultiplication under coefficient ring maps.
Applying this fact to images of degree-one monomials proves that the coordinate
scalar-extension algebra map is a bialgebra map.

Agreement on an additive-monoid generating set determines an algebra morphism
out of a monoid algebra. The proof forms the additive submonoid of degrees where
the two maps agree and proves that it is the whole monoid. Given a finite set
of generators and an additive character map `g`, `generatorCoefficientProduct`
is the product, over those generators `n`, of the coefficient of degree `g n`
in `f (single n 1)`. If this product becomes a unit in any commutative
`R`-algebra `A`, every selected coefficient becomes a unit. The imported
unit-coefficient lemma for group-like elements then makes the scalar extension
agree with the monoid-algebra map induced by `g` on every generator, hence
everywhere. This argument includes the zero ring and requires no reducedness,
flatness, or injectivity of the coefficient map.

For additive commutative groups `N` and `M`, a bialgebra equivalence of their
group algebras over a field induces an additive group equivalence
`characterEquiv`. The forward and inverse maps are Mathlib's character maps
of the bialgebra equivalence and its inverse. The two inverse identities follow
by applying the injective degree-one monomial map and the corresponding
bialgebra inverse identities. For a map specialized to a field, the coefficient
in the selected character degree equals one, as follows by taking that
coefficient in Mathlib's monomial formula.

The theorem `exists_principal_isomorphism_certificate` assumes that `N` is
finitely generated as an additive monoid and that the canonical scalar
extension of `f` to a field `K` is bijective. It produces `r : R` whose image
in `K` is nonzero and such that, for every commutative `R`-algebra `A` in an
independent universe, invertibility of the image of `r` forces the scalar
extension of `f` to `A` to be bijective. The proof selects a finite monoid
generating set and the character equivalence of the field specialization.
The coefficient product specializes to one. After inverting it, the preceding
agreement result identifies the scalar extension with the actual monoid-algebra
isomorphism induced by that character equivalence. No finite generation of
`M` is required in the statement.

These constructions and proofs are derived internally from the standard
monoid-algebra bialgebra, Mathlib's classification over fields, and the
arbitrary-ring coefficient lemmas in `DiagonalGroupLikeCoefficients`.
They assert neither a geometric open isomorphism locus nor the final Hom
representability theorem.
