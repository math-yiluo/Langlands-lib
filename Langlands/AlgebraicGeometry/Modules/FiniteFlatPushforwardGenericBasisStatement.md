# Generic free charts with native finite-flat rank

For any finite flat morphism of actual schemes with integral locally
Noetherian target, the actual module sheaf `f_* O_X` is free on some
nonempty affine open of the target. For any specified target point `x`,
the free sheaf has exactly `f.finrank x` generators. The open is not
required to contain `x`.

The index type is a universe lift of `Fin (f.finrank x)`, and the
conclusion is an actual isomorphism of module sheaves on the open
subscheme. The statement includes rank zero. It supplies no chosen
canonical basis or numerical degree certificate.

This is internally derived from the finite flat structure-module
pushforward comparison, finite-presentation descent of a basis from
the fraction field to one principal localization, the tilde equivalence
on affine schemes, and preservation of free sheaves under restriction.
It is a geometric prerequisite for comparing Euler polynomials on a
dense open; it asserts no leading-coefficient or polarized-rank formula.
