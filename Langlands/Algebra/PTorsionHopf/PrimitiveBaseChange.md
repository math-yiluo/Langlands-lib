# Primitive defects and scalar extension

This internal tensor-algebra adapter expresses primitive elements of a commutative bialgebra as the kernel of the linear map `comul - (1 tensor -) - (- tensor 1)`. The counit condition follows from the comultiplication condition by Mathlib's primitive-element theorem.

The module constructs the canonical linear equivalence between the scalar extension of the tensor square and the tensor square of the scalar extension. Under this equivalence, the scalar extension of the primitive defect equals the primitive defect of the scalar-extended bialgebra. Hence its kernel is exactly the primitive submodule after scalar extension.

These are derived formal identities using Mathlib's tensor-product coalgebra and bialgebra structures. No classification or field-descent premise is used.
