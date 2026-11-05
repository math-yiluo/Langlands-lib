# Actual fixed-exponent characters over arbitrary bases

`exponentCharacter S I m` is the actual homomorphism from the split torus
with finite coordinate index `I` over a scheme `S` to its multiplicative
group. It is the sum, in the additive notation for commutative
group-scheme homomorphisms, of the coordinate projections with
coefficients `m j : ℤ`. Its value on every actual test-scheme point is
the monomial `∏ j, t j ^ m j`.

The construction uses a fixed exponent on the whole base and makes
no claim that every character over a disconnected base is of this
form. Over fields, the construction agrees with the existing inverse
of `characterLatticeEquiv`.

`exponentCharacter_baseChange` proves compatibility with every
base-change morphism, using the canonical split-torus comparison and
the existing compatibility of each coordinate projection. The proof
uses preservation of finite sums and integral multiples by the
character pullback homomorphism.

Over a commutative base ring, the character value on every actual
affine test point is its exponent monomial. Consequently
`exponentWeightSpace_eq_weightSpace_exponentCharacter` identifies the
relative exponent-weight submodule with the Library's existing actual
all-test character weight submodule for this character.

The provenance is internal: this generalizes the fixed-exponent
construction and point computation already used by the field
character-lattice interface, using only actual split-torus coordinate
projections and their published base-change compatibility. It supplies
character comparisons for the relative adjoint-weight argument, and
proves no reductive-locus openness theorem.
