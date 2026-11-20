# Coefficient and torsion projections for diagonalizable groups

`Diagonalizable.coefficientProjectionOver` is the spectrum of the group-algebra coefficient map, viewed over the original base. Its structural equality follows by evaluating both composite ring maps on a coefficient monomial. `baseChangeIso_inv_fst` identifies this map with the pullback projection composed with the inverse of the canonical diagonalizable base-change isomorphism. To prove the equality, the Lean proof evaluates both points on every character. Applying the canonical spectrum section isomorphism identifies each evaluation with the same monomial.

`torsionIso_inv_comp_ι` identifies the composite of the inverse torsion isomorphism and the torsion inclusion with restriction along the lattice quotient by the subgroup of multiples of the order. The comparison follows from the point-model construction of `torsionIso`. `torsionIso_inv_comp_ι_left` specializes the comparison to the split-torus lattice and gives the quotient map on the underlying spectra.

These are internal comparisons derived from the Library's character-valued point models. They identify the maps used in affine coefficient descent with the actual base-change and torsion maps.
