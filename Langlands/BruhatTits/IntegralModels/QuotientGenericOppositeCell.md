# Generic opposite-cell factors from a quotient reduction

Worker 248. Internal supporting result at arbitrary universe `u`.

Let `R` be a commutative local domain with specified fraction field `K`,
`D` supplied smooth affine relative-component model data, and `Q` supplied
special-fibre quotient data satisfying `Q.IsReductiveQuotient`. For an
integral cocharacter `χ` of the neutral model and an actual integral
section `x`, assume that the reduction followed by the specified quotient
projection lies in the opposite dynamic unipotent subgroup of the
residue-base change of `χ` followed by that same projection. Then the
specified generic image of `x` has opposite-unipotent and parabolic factors
for the generic-base change of `χ` followed by the model's generic
identification.

The proof derives connectedness of the neutral special fibre from the
supplied connected-fibre property. It identifies the actual kernel of the
quotient projection with the supplied smooth connected unipotent radical
using `IsFppfQuotient.kernelIso`. The scheme isomorphism transfers
connectedness, and `IsUnipotent.of_iso` transfers unipotence. Smoothness of
the projection is `projection_smooth`; its surjectivity is part of the
supplied fppf-quotient predicate. Connected reductivity supplies smoothness
and connectedness of the actual quotient.

The dynamic affine representatives give actual opposite-unipotent and
parabolic models over both the integral ring and the residue field.
Representability lifts the given quotient reduction into the
opposite-unipotent representative. Together with the identity parabolic
point this gives quotient opposite-cell coordinates.
`oppositeCell_section_lifts_iff_quotient_reduction` lifts these coordinates
to the integral cell. Finally `generic_oppositeCell_of_integral_lift`
transports them through the specified generic-fibre identification,
preserving their exact product.

`genericOppositeCellFactorPairOfQuotientUnipotent` selects such a pair,
retaining both subgroup memberships and the product identity in its
subtype. This is an internal composition of the imported integral cell,
fppf quotient and generic-coordinate APIs. It does not assume a lift of
arbitrary rational quotient points, Henselianity, perfection of the residue
field or a root-survival criterion.
