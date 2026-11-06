# Extremal coordinate lines of dynamic parabolics

This derived construction starts with an actual matrix representation `ρ`
over an arbitrary commutative ring `R`, a cocharacter `ν`, and an equality
`ν ≫ ρ = diagonalCocharacter e`. The equality is one of group-scheme
homomorphisms. No faithfulness assumption is imposed on `ρ`.

Functoriality of dynamic parabolics and the proved description of those
of the general linear group give
`pointMatrix_entry_eq_zero_of_mem_parabolic`: the matrix entry `(a,b)`
vanishes whenever `e a < e b`, on every relative scheme test. A supplied
representative `i : H → G` of the dynamic parabolic therefore preserves
the coordinate line at `j` when `e j` is strictly greater than every other
coordinate weight. When `e j` is strictly smaller, the dual representation
preserves the coordinate line at `j`.

The intermediate `preservesCoordinateLine_of_column_eq_zero` upgrades
column vanishing to an eigenline with a global unit scalar. Applying the
same vanishing statement to the inverse point shows that the two diagonal
entries multiply to one; matrix multiplication proves this by eliminating
all other summands. This works over arbitrary rings and arbitrary test
schemes.

`maximumWeightCharacter` is the existing coordinate-line rational
character of the restricted representation. `minimumWeightCharacter`
is the negative of that character for the dual representation. The two
action theorems give, respectively, the eigenvector and eigen-covector
laws for the standard coordinate vector and covector. For the covector
law, the dual-line action at the inverse point removes the inverse
transpose. The evaluation theorems identify both character values with
the original matrix's `(j,j)` entry.

All conclusions concern every original test scheme, including nonaffine
and nonreduced schemes. The construction supplies actual rational
characters and their eigen-laws from the diagonal-cocharacter equality
and strict coordinate inequalities. It does not construct the
representation, prove that an extremal weight has multiplicity one, or
identify its weight with negative rho. It supplies no general
highest-weight existence or Steinberg irreducibility theorem.
