# Scalar comparison of arbitrary invariant sesquilinear forms

Author: Worker 89.

`Langlands.InvariantSesquilinearScalarStatement.{uG,uV}` states that on an
irreducible admissible complex representation, every nonzero invariant
sesquilinear form is a nonzero complex scalar multiple of a supplied invariant
positive form. It is a Prop-valued definition; this module supplies no proof.

The group and carrier universes are independent. The group is a topological
group whose compact open subgroups are cofinal among open subgroups. The
representation carrier has only its additive group and complex module
structures. The form is conjugate-linear in its first argument and linear in
its second. The statement assumes neither symmetry nor nondegeneracy of that
form, and its scalar is complex. The reference positive form and admissibility
are explicit hypotheses.

This is a derived prerequisite for the compact-integral proof of
`Langlands.Classification.BernsteinUnitaryProductFactorUnitarity`. Its
provenance is the Library's `InvariantPositiveForm.smoothDualEquiv`
(`Unitary/HermitianDual`) and `admissibleSchur_scalarEndomorphism`
(`Smooth/Schur/Proof`). An arbitrary invariant sesquilinear form defines a
conjugate-linear map into the smooth dual. Composing with the inverse of the
positive-form identification gives an equivariant linear endomorphism, to
which admissible Schur applies. The nonzero hypothesis forces the resulting
scalar to be nonzero. This is an internal derived statement, not a claim of a
separately numbered result in the original literature.
