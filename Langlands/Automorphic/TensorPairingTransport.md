# Tensoring and transporting nonzero invariant bilinear forms

This internal construction for the proof of
`CuspidalTransposeInverseContragredientStatement` uses Mathlib's tensor bilinear
form and its transport across a complex-linear equivalence. On elementary
tensors, the form is the product of the two factor pairings. If both
factor forms are nonzero, witnesses for their nonzero values give a
nonzero product value, so the tensor form and its transported form are
nonzero.

The module proves the covariance rules needed to assemble local
inverse-transpose pairings. Independent invariance on the two factors
implies invariance under the corresponding tensor operators. A Lie
skew-invariance identity on either factor gives the same identity on the
tensor product. All identities are proved first on elementary tensors
and extended by bilinearity.

When a tensor equivalence carries those tensor operators to actual
operators on its target, the transported form satisfies their group
invariance and infinitesimal skew-invariance identities. The two
operators in each identity are supplied independently, so this applies
in particular to an operator and its inverse-transpose twist without
adding a new assertion about that twist. Existence of all factor forms,
the tensor equivalence and its covariance remain explicit inputs.
