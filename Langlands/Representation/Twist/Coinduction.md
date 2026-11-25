# Character twists and the actual coinduced representation

This module constructs an explicit representation equivalence for the
fixed-Haar duality argument.

For a homomorphism `φ : H →* G`, an ambient unit-valued character `χ`, and
an actual representation `ρ` of `H`, `coindTwistEquiv` identifies coinduction
of the `χ.comp φ` twist of `ρ` with the `χ` twist of its coinduction.
On the actual space of equivariant functions, the map sends `f(g)` to
`χ(g)⁻¹ • f(g)`. Multiplication by `χ(g)` gives its inverse. The subgroup
equivariance identity follows from multiplicativity of the character.
Right translation gives the intertwining identity.

The equivalence is algebraic over any commutative coefficient ring and
preserves independent group, subgroup and carrier universes. It uses no
finite-index or continuity hypothesis. In the finite-index case this is
the equivariant-function model used by the existing finite-dimensional
induction construction.

This is internal derived algebra from the actual `Representation.coind`
and scalar `twist` definitions. It asserts no Fourier equation, degree-zero
generation, or dual-induction identity.
