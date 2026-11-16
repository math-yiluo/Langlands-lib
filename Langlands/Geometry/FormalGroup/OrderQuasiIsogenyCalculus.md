# Inverse and square calculus for actual order-linear quasi-isogenies

This internal module proves the identity, associativity, inverse and
cancellation laws for the existing actual full-order `QuasiIsogeny` type.
The scalar ring `O` is a commutative domain, `F` is its fraction field,
the coefficient ring is any commutative `O`-algebra, and the acting order
is any `O`-algebra ring. All coordinate types are finite and may differ.
No nilpotence, height or representability hypothesis is needed.

The proofs use equality of actual rational formal maps. Extensionality of
quasi-isogenies reduces identity, associativity and cancellation of inverse
pairs to the corresponding tensor-Hom equations and the stored two-sided
inverse equations. Inverting twice and reversing a composite retain exactly
the same forward and inverse maps.

`square_reverse` starts from `g f = b a` and proves
`g⁻¹ b = f a⁻¹`. It inserts the inverse pair for `a`, uses the supplied
square, and cancels the inverse pair for `g`. `square_paste` combines
`g f = b a` and `g' b = c a'` to obtain
`(g' g) f = c (a' a)`, using associativity and these two equalities.
These are equalities of actual full-order quasi-isogenies, including their
uniquely determined inverse maps.

The provenance is internal: all constructions and inverse equations are
already in `OrderRationalMorphism`. This module supplies their algebraic
calculus for later framing-square arguments. It asserts no height
additivity, coefficient-descent theorem or formal-moduli comparison law.

`CommutingSquare` packages four specified actual full-order
quasi-isogenies and their actual commuting-square equation.
`CommutingSquare.reverse` constructs the square with the two vertical
maps inverted, using `square_reverse`. `CommutingSquare.paste` takes
two such squares and equality of their shared horizontal map; it
constructs the square with composite vertical maps, using
`square_paste`. Thus these constructions retain the specified formal
rational maps, not merely existence of a square.
