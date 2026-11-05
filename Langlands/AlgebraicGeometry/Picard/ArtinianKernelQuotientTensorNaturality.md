# Tensor naturality of the actual elementary ideal cohomology quotient

Let `f : X ⟶ Spec k` be an actual scheme, `K` a field with `Algebra k K`,
and `q : A → B` an elementary surjection of actual augmented Artinian tests.
Let `W` be a `K`-subspace of its actual kernel, with the canonical descended
residue action, and `r : AQ → B` the actual reduction from the quotient test.
Everything has arbitrary common universe `u`.

`residueCohomologyTensorQuotientMap f q W n` is the actual linear map
`id ⊗ kernelLinearMap q W` on
`H^n(X_K, O_X_K) ⊗[K] Kernel q`.
It uses the published actual kernel quotient and the actual residue-fibre
cohomology. Its definition requires neither flatness nor properness.
For specified finite bases `b` and `c` of the two actual kernels,
`residueCohomologyTensorQuotientMap_coordinates` gives the finite matrix
formula. It specializes the existing general tensor-coordinate formula to
the identity on the residue cohomology factor. Empty finite bases are allowed.

Assume `Flat f` for the following ideal comparisons.
`residueProductCohomologyCoordinates_productCohomologyEquiv` identifies the
new residue-product coordinates of the existing product presentation of
actual ideal cohomology with the independently constructed
`idealCohomologyCoordinates`. This is definitional from their compositions
of the same isomorphisms.
`idealCohomologyCoordinates_quotient` proves the finite coefficient formula
for the independently defined `cohomologySemilinearMap` on the unchanged
actual ideal-cohomology groups. Its proof combines the published actual
product-to-ideal cohomology square with the quotient product cohomology
coordinate formula. Properness is not needed for these two lemmas.

Assume also `IsProper f` for the following results, which use the existing
residue-field module structures on the unchanged actual ideal-cohomology
groups. `vectorTensorCoordinates_idealCohomologyTensorEquiv` identifies the
coordinates of the independently defined `idealCohomologyTensorEquiv` with
`idealResidueCohomologyCoordinates`; it cancels the tensor-coordinate
isomorphism with its inverse.

`idealCohomologyTensorEquiv_quotient` proves, for every `n : ℕ` and every
actual ideal-cohomology class `x`, the equality

`idealCohomologyTensorEquiv f r c n (cohomologyLinearMap f q W n x)`

`= residueCohomologyTensorQuotientMap f q W n (idealCohomologyTensorEquiv f q b n x)`.

Both source and target use the existing descended `K` actions; these are
explicit local instances in the theorem type. The quotient cohomology map,
its source and target groups, and the tensor comparisons are independently
constructed in the imported modules. The proof applies the injective target
tensor-coordinate equivalence, compares each coordinate using the tensor
matrix formula and the ideal-coordinate quotient formula, and identifies
the underlying functions of the semilinear and residue-linear maps by
definition.

The provenance is internal: this is a consequence of the actual finite
product-to-ideal comparison, the scalar-lift cohomology coordinate calculation,
and finite-basis tensor coordinates. No `K`-algebra structure on the test
ring, residue-field section, kernel-dimension restriction, or additional
obstruction hypothesis is assumed. The identification is in every
nonnegative degree, including the obstruction degree two. Naturality of
the actual lifting obstruction, the formal family construction, and the
exact field Picard-stack atlas theorem remain further obligations.
