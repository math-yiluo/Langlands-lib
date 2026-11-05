# Levi assembly from reductive vector-kernel splitting

This internal construction composes three published Library interfaces:
`ReductiveUnipotentQuotient`, the characteristic-zero unipotent-extension
induction, and `RelativeRoot.splitUnipotentStableVectorSubgroup`.
It retains exactly one global proposition as an explicit input:
`CharacteristicZeroReductiveVectorExtensionStatement.{u}`. This module
does not prove that proposition or the unconditional Levi target.

Over any characteristic-zero field `k : Type u`, let `G` be a smooth
connected affine group scheme and let `D : ReductiveUnipotentQuotient G`.
`D.exists_leviSection` constructs an actual group-scheme homomorphism
`j : D.quotient ⟶ G` satisfying `j ≫ D.projection = 𝟙 D.quotient`,
conditional on the vector-extension input. The proof installs smoothness
and surjectivity of the projection and connectedness of its full
scheme-theoretic kernel from the fields of `D`. It then applies
`CharacteristicZeroUnipotentExtension.exists_section`, supplying the
published stable-vector theorem and the retained vector-extension input.
The quotient's connected reductivity and the actual kernel's unipotence
are also fields of `D`. `D.leviSection` chooses this homomorphism;
`D.leviSection_comp` proves its section equation. The homomorphism and
equation are over the original ground field.

`characteristicZeroLeviDecomposition_of_reductiveVectorExtensions` has
the exact published universe-polymorphic Levi proposition as its
conclusion, with the vector-extension proposition as its explicit
premise. It supplies the same unipotent-extension theorem, with the
stable-vector premise discharged, to
`characteristicZeroLeviDecomposition_of_reductiveExtensionSections`.
That published reduction constructs the actual radical quotient over
the original field and provides the target's smooth, connected,
unipotent full kernel. In particular, this adapter introduces no
algebraic-closure or splitness hypothesis on the target's field or
reductive quotient.

The provenance is derived composition of the three imports. No
additional result from the literature is invoked here. The supporting
modules record the radical-quotient and dimension-induction arguments
and their source provenance. All conclusions of this module remain
conditional on the unproved vector-extension input.
