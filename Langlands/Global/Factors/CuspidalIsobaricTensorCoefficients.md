# Finite detection by Eisenstein coefficients

`HasCoefficientDetection` specifies the finite coefficient condition on
an invariant submodule of the free operator module on a family of seeds.
The specialization is defined on that submodule and is surjective. The specified coefficient
maps to actual stable automorphic functions detect each vector with nonzero
specialization.

For a simple target, `exists_freeIntertwiner_of_coefficientDetection` applies
`EisensteinJet.exists_subquotient_of_coefficients` to the coefficient maps
restricted to the submodule. `exists_freeIntertwiner_of_operatorModuleSurjection`
restricts scalars to the complex numbers to turn the operator-module quotient
into a surjective intertwiner of the full free operator action. The action on
stable forms is the pullback of their actual operator action.

`CuspidalInducedFiniteTensor.hasTensorRealization_of_coefficientDetection`
uses the proved irreducibility of the exact isobaric constituent tensor.
The induced intertwiner then realizes the prescribed finite and
archimedean constituents together as `HasTensorRealization`.

This is the algebraic coefficient step in Langlands (1979), Proposition 2
and Lemma 7, printed pp. 205–206 (Corvallis I PDF pp. 200–201). It uses the
finite coefficient condition as an input.
