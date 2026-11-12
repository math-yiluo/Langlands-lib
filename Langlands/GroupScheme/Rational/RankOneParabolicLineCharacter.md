# Positive rank-one relations for actual parabolic line characters

This internal derived result connects the actual coordinate-line character to
the integral relative-root lattice. It uses the proved geometric line-weight
positivity, actual rank-one reversing normalizers, and integral character
comparison modulo ambient rational characters.

`HasPositiveIntegralRootCharacterRelation i alpha psi` asserts that there are
positive natural integers d and b and an actual rational character eta of G
such that d psi equals the restriction of eta plus b alpha, as an exact
equality of integral torus characters.

The algebraic character on a preserved coordinate line restricts naturally
along any group-scheme homomorphism. The proof compares its values on every
scheme test; both global unit scalars are the same diagonal matrix entry.
Consequently, the integer of the coordinate-line character after restriction
along a torus cocharacter is exactly the original torus lattice pairing.
Both are `gmEndEquiv` applied to the same composed algebraic character.

The torus preserves the selected line whenever the dynamic parabolic of one
of its cocharacters does. The torus image lies in the actual dynamic
centralizer, hence in the parabolic. Representability lifts that torus
homomorphism into the parabolic, and the all-test line action restricts along
the lift.

Now let G be a connected reductive group over an arbitrary field, with an
actual maximal split torus i, a generic cocharacter nu and a singleton actual
simple-relative-root set containing alpha. Assume a finite matrix
representation has a coordinate line preserved by the actual dynamic
parabolic for `normKernelCocharacter i nu`, but not by the entire G. Supply
representatives of that parabolic and its actual opposite dynamic unipotent.
The final two theorems state torus-line preservation explicitly; the preceding
adapter derives it from the parabolic-line preservation assumption.

The actual rank-one Weyl theorem gives a rational normalizer reversing the
corrected cocharacter. The geometric proper-eigenline theorem makes the
original algebraic line-character integer strictly positive. The character
restriction identity identifies that integer with the actual torus pairing
on the corrected direction. This discharges the positivity premise in the
integral rank-one character comparison, proving the exact positive relation.
There is no diagonal-basis premise or splitness assumption on G.

The relation retains an actual ambient rational character. No proportionality
of the full torus line character with the root alone is asserted. This unit
does not construct a representation with the exact parabolic stabilizer,
identify the chosen parabolic with the standard rank-one parabolic, establish
adelic height estimates, or prove chamber coverage.
