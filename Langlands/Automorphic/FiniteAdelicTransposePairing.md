# Nonzero inverse-transpose forms for finite adelic representations

This internal construction for the cuspidal contragredient of dual cusp forms
(`CuspidalTransposeInverseContragredientStatement`) supplies the finite-factor form
used by the actual finite/infinite intrinsic global pairing assembly.
It applies to any irreducible admissible complex representation of the
actual finite adelic group of positive-rank general linear matrices.
The number-field and carrier universes are independent.

The published local Gelfand--Kazhdan theorem is first transported from
the canonical p-adic matrix-group topology to the actual completion
topology, using the published equality of those topologies. Evaluation
of its smooth-dual equivalence gives a nonzero local transpose form.
At a spherical place, the preceding compact-open fixed-line
normalization construction rescales the form to value one on the
prescribed nonzero reference.

The published actual Flath factorization gives irreducible admissible
local factors, nonzero spherical references outside a finite
exceptional set, and one-dimensional fixed spaces there. Choose
arbitrary nonzero local forms on the exceptional set and normalized
forms elsewhere. The completed actual restricted-tensor pairing
construction gives a nonzero form on the tensor product.

Its componentwise invariance is exactly finite adelic inverse-transpose
invariance because inverse transpose commutes with the actual local
projections. Transport through the supplied Flath equivalence gives
the required form on the original representation. The final
`pairing` definition chooses it together with its invariance and
nonzeroness properties.

The provenance is internal assembly from published local GK, topology
comparison, and Flath theorems and the implemented normalization and
restricted-tensor constructions. It proves finite adelic form
existence, while the real and complex archimedean existence inputs
of the full global target remain separate obligations.
