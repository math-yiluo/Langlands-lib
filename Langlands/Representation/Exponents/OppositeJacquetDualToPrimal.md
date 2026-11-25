# Primal occurrence of an actual opposite dual Jacquet exponent

`Langlands.oppositeJacquetDualToPrimal` takes an admissible general linear
representation `A` and `hχ : T.IsDualJacquetExponent B A χ`. It concludes
that `χ` is a generalized eigencharacter of the actual
`T.splitCentreOppositeJacquet B A` action. The field and source carrier
universes are independent, and the source has no irreducibility
hypothesis.

Published standard opposite Jacquet admissibility gives admissibility of
the actual Levi representation. Published compact-open cofinality for
that Levi supplies the local condition for
`admissibleCentralDualToPrimal`. The block-scalar map factors through the
actual center. The ordinary transpose eigenspace clause `hχ.2` is exactly
the algebraic input of that published conversion theorem. Its conclusion
is definitionally the displayed primal action, with the same character
and one uniform natural power for the nonzero vector it supplies.
The open-kernel clause `hχ.1` is retained by the caller and is not needed
for this conversion.

This is internal derived content. It imports the published conversion
proof `admissibleCentralDualToPrimal` (module
`AdmissibleCentralDualToPrimalProof`), which takes a finite-fixed-space
route. It asserts one primal
occurrence, without a global decomposition or finite spectrum claim.
