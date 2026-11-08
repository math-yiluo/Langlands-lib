# Elementary generation of prescribed Hermitian Levi elements

This internal continuation of `HermitianRootMiddleGeneration` adjusts its
unspecified nonzero hyperbolic coefficient to a prescribed determinant-one
Levi element. The field and finite middle-index universes are independent;
all characteristics and the empty middle index are allowed.

`leviMatrix_det` computes the determinant of the existing block matrix as
`a * (det(T) * bar(a)⁻¹)` using the two block-triangular determinant identities.
`leviScalarAdjustment a b ha hb` is the actual unit with value `a/b` for
nonzero `a` and `b`. If the two Levi matrices with common middle block `T`
both have determinant one, `leviScalarAdjustment_fixed` proves this unit is
fixed by the involution. Indeed, the determinant identities give
`a*det(T)=bar(a)` and `b*det(T)=bar(b)`, and cross multiplication proves
`bar(a)/bar(b)=a/b`.

`diagonalMatrix_eq_leviMatrix` identifies the existing hyperbolic diagonal
matrix for an involution-fixed unit with the Levi matrix having that top
coefficient and identity middle block.

`specialUnitary_levi_mem_elementarySubgroup` assumes anisotropy of `H`, a
supplied nonzero trace-zero scalar `s`, and an actual special-unitary element
`g` whose underlying matrix is `leviMatrix a T` with `a≠0`. Form preservation
gives the standard-column pairings of `T`. The preceding middle-generation
theorem gives an actual elementary lift `h` of `T` with some nonzero top
coefficient `b`. Containment of the elementary subgroup in the special
unitary subgroup gives determinant one for `h`. The fixed ratio `a/b`
therefore has an elementary diagonal matrix by the established trace-zero
diagonal-generation theorem. Multiplying that diagonal by `h` gives exactly
`g`, by the Levi product identity and `(a/b)*b=a`. Subgroup closure proves
the asserted elementary membership.

The result proves prescribed Levi generation with the stated hypotheses.
Stabilizer reduction, full-group generation, group-scheme comparisons and
the unrestricted local Kneser–Tits theorem remain separate obligations.
