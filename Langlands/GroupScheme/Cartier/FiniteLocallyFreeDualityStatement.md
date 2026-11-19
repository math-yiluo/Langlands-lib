# Finite locally free Cartier duality over an affine base

Demazure and Gabriel, *Groupes algébriques*, Tome I (1970), Chapter II,
§1, no. 2, 2.10(a) and the proposition in 2.10(d), printed pp. 156–158
(PDF pages 186–188), define the Cartier dual functor by relative characters.
They identify the dual of a commutative finite locally free scheme-monoid
as finite locally free and identify its canonical biduality map as an
isomorphism. The Lean target uses the commutative group scheme case.

`FiniteLocallyFreeCartierDualityStatement` takes a commutative group scheme
`G` over the spectrum of a commutative ring. Its structure morphism is
finite, flat and locally of finite presentation. It asserts the existence
of a commutative group scheme `D` with these same three properties and a
natural isomorphism of additive group functors from the points of `D` to
the Library's actual relative character presheaf of `G`.

The natural isomorphism from the points of `G` to the characters of `D`
must realize evaluation. For any test scheme `T`, its character of `D`
associated with `x` evaluated at `y` has the same value as the character of
`G` associated with `y` evaluated at `x`. This equation uses the actual
relative evaluation to the multiplicative group and specifies the
canonical biduality identification.

This proposition is a proof target. It supplies the outstanding
representability and biduality assertions for the finite scalar-power
kernel group schemes used in the Drinfeld tower.
