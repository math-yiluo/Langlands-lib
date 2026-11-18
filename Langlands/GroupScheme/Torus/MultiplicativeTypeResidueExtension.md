# The residue-field step for multiplicative-type extensions

Worker 875.

`fieldMultiplicativeType_of_relativeDiagonalizable` converts a relative
full-character diagonalization over a field into the field-level
multiplicative-type predicate. The affine-relative diagonalizable comparison
identifies the actual models; the field itself is a splitting extension.

`fieldMultiplicativeType_of_extension` applies the exact
`MultiplicativeTypeFieldExtensionStatement`, retained as an explicit premise.
The middle-group alternative in the host statement suffices: a commutative
middle group meets the field theorem's first alternative, and a connected
middle group has connected surjective quotient, meeting its other alternative.
The theorem imposes no extra connectedness hypothesis on a kernel or base.

`residueFiber_fieldMultiplicativeType_of_extension` applies this argument at
every actual scheme residue fibre of an extension with relative diagonalizable
endpoints. The actual monomorphism and fppf quotient survive residue-field
base change, as do the endpoint diagonalizations. The supplied pointwise
alternative is unchanged.

This is an internal conditional application of the exact field statement,
field/relative diagonalizable comparisons and published quotient base change.
It does not prove that statement or the host target unconditionally.
