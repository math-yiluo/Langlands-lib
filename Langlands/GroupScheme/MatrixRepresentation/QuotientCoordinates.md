# Actual quotient representations in split coordinates

This internal construction supplies actual group-scheme quotient representations
for the composition-factor argument in the proof of KP Lemma 2.2.11 (printed
pp.72–73, PDF pp.103–104, *Bruhat–Tits theory: a new approach*, 2023). It is a
derived linear-algebra construction, rather than a separately numbered assertion
of that source.

For a commutative base ring, `IsQuotientCoordinates ρ Q D` says that the constant
projection matrix `Q` intertwines the ambient matrices with `Q ρ D` on every
relative scheme test. Given `Q D = 1`, these latter matrices form a natural
monoid homomorphism. The general-linear point equivalence and `homOfPoints`
therefore construct `quotientCoordinates`, an actual representation. Its point
matrices and the projection intertwining identity are proved on every test.

Over an arbitrary field, `exists_quotient_split_coordinates` chooses a finite
basis of the vector-space quotient by a subspace and a linear section of its
surjection. It gives a split projection with exactly that subspace as kernel.
If the kernel is stable in the published all-affine-tests sense and the group
is affine, `IsStableSubspace.isQuotientCoordinates` proves the required
all-scheme-tests equation. It uses split coordinates `B,C` of the stable
subspace: `Q B = 0`, and `B C` fixes the image of `1 - D Q`. The all-test
stability of `B,C` then makes `Q ρ (1 - D Q)` vanish.

`QuotientRepresentation ρ V` records the actual representation, its finite
dimension, a split surjective projection, the exact kernel and an all-affine-tests
intertwiner. `nonempty_quotientRepresentation` constructs it from stability.
The split section proves `projection_surjective`, and `isSubquotientOf` realizes
the quotient through the identity embedding of the ambient representation in the
published actual-subquotient interface.
Empty ambient or quotient dimensions are included. No reducedness, smoothness,
connectedness, reductivity or characteristic restriction is used. This unit
does not yet construct a composition series or prove its kernel finite.
