# Actual matrix coefficients at rank one

This internal algebraic construction supplies the coefficient-space step in
the Tate branch of `RankOneMatrixFunctionalEquationComparisonStatement`.
It uses the published full rank-one functional-space computation and the
linear-dual argument from `RankOneCharacterReductionProof`. It assumes no
irreducibility of the original carrier.

`rankOneCarrierComplexLine` uses triviality of the rank-one unipotent group:
the standard functional space is the full algebraic dual. Full Whittaker type
identifies this dual with the complex numbers. The published
`dual_symm_one_bijective` then gives a linear equivalence from the original
carrier to the complex numbers.

`linearForm_bijective_of_complexLine` proves that a nonzero linear functional
on a complex line is bijective, by writing each vector as a scalar multiple
of the vector corresponding to one. Using the specified nonzero functional
as this coordinate, `rankOneModelEvaluationEquiv` identifies the actual
coefficient image with the complex numbers by evaluation at the identity.
Its inverse sends a complex coordinate through the inverse original
functional and then through the actual surjective model map.

`exists_openSubgroup_all_fixed_of_complexLine` takes a smooth stabilizer of
the vector corresponding to one and proves it fixes every vector.
`smoothDualOfComplexLine` uses the same subgroup, including closure under
inversion, to make any algebraic linear form an actual smooth-dual vector.

`glModelFunction_mem_biSmooth_rankOne` uses evaluation at the identity as the
smooth functional and the supplied model vector as a smooth vector. Its matrix
coefficient is exactly the original model function by right translation.
`biSmoothMatrixCoefficients_rankOne_model` proves equality for the entire
coefficient span: any generating coefficient is the model function associated
with a scalar multiple of its vector, because evaluation is a coordinate on
the line. The reverse inclusion is the preceding explicit coefficient.

The result agrees with the rank-one description on JPS 1979, printed page
181, but is derived directly from the published algebraic APIs. It proves
neither a functional equation nor existence of analytic data. The topology is
used only for the smooth-vector conditions; the construction does not choose
any measure or Fourier normalization.
