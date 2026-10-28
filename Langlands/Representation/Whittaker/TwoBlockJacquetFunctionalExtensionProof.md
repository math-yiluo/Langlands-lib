# Extending the cell integral to the full induced representation

`Langlands.Whittaker.twoBlockJacquetFunctionalExtension` proves the closed
`TwoBlockJacquetFunctionalExtensionStatement`. It constructs a representation of the full upper-unipotent group
on the actual cell submodule, using its proved stability. Its inclusion into
the restricted induction is an injective intertwiner.

The scalar integrand is a linear map of the cell vector. Cell integrability
makes its ordinary integral a complex linear functional. Full-unipotent
Jacquet covariance supplies the standard-character property on this restricted
representation.

The standard character is continuous on a nonarchimedean group, so it has open
kernel; cosets of this kernel establish local constancy. The upper-unipotent
group is a limit of compact subgroups and the ambient induced representation is
smooth. The existing smooth subgroup-functional extension theorem therefore
extends the cell integral to a standard Whittaker functional on the actual
full induction, agreeing on every cell vector.

This construction does not identify the extension with a convergent ordinary
integral outside the cell submodule, and it does not assert uniqueness or
nonvanishing. It supplies the functional-extension prerequisite, not the
prescribed-value host extension formula.
