# Diagonally equivariant equations of actual formal kernels

`diagonalScaleJet` scales each variable of a rectangular characteristic-power
jet by its specified weight. The scaling agrees with the actual pullback of
an endomorphism whose formal coordinate map is diagonal. Evaluating the
linear series on the universal jet point gives this equality on generators.

If a formal homomorphism intertwines diagonal actions given by the same
weights, the images of the target variables in the source jet have their
respective weights. Lift these images to polynomials and average over one
period of the diagonal action. The average keeps the chosen jet image and
has the specified weight as a polynomial. Restricting to a smaller
characteristic-power width then identifies the equations with the image of
the target augmentation ideal. Those are the actual kernel equations.

`finrank_modEq_of_diagonal_formal_kernel` applies the dimension congruence
when all weights have common order `m`, invertible in the coefficient field.
Choose two widths beyond the bound for the represented kernel. An exponent
congruent to one modulo `m` gives the equivariant polynomial perturbation.
The modeled kernel's rank is consequently one modulo `m`.

The construction is derived infrastructure for the distinct special tangent
characters of Drinfeld 1976, §2A, printed p. 109. Matching the weights to a
primitive residue unit of the unramified subfield is the next step in
specializing the congruence to division-degree heights.
