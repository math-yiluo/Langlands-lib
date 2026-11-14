# Integral opposite-cell coordinates detected in a special-fibre quotient

This internal construction combines the original-field inverse-image theorem
for dynamic opposite cells with the section-lifting property of open charts
over a local ring. The integral base `A` is a local domain with fraction field
`K`. The supplied integral model `M` is smooth; its special fibre is connected.
There is no Henselian or algebraically closed residue-field hypothesis.

Fix an integral cocharacter `χ` and any actual integral representatives of
`U_M(-χ)` and `P_M(χ)`. Let `q` be a smooth scheme-surjective homomorphism
from the special fibre to a smooth connected affine residue-field group,
with connected unipotent full scheme-theoretic kernel. Supply any actual
representatives of the corresponding opposite dynamic factors in this quotient.

`oppositeCell_section_lifts_iff_quotient_reduction` proves that an original
integral section factors through the integral opposite cell if and only if
its reduction followed by `q` has coordinates in the quotient opposite cell.
The source cell is open by `dynamicBaseOppositeCell`. The published
`section_lifts_iff_reduction_lifts` reduces the claim to the actual special
fibre. Dynamic subgroup representability commutes with that base change,
including the negative sign. The canonical product comparison identifies
the base-changed product chart with multiplication of the two base-changed
factors. Finally `Dynamic.oppositeCell_exists_lift_iff` identifies this cell
with the inverse image of the quotient cell. Each factorization remains an
actual morphism over its stated base.

`oppositeCellSectionLift` chooses integral source coordinates from supplied
quotient-cell coordinates of the reduction. Its `_comp` theorem states that
their original integral product is exactly the given section.

The provenance is internal composition of the cited Library results and the
proved dynamic kernel-cell construction. This is an integral-coordinate
bridge for the depth-zero opposite-factor argument. Construction of a suitable
quotient, a translated-cell normalizer and the host theorem remain separate.
