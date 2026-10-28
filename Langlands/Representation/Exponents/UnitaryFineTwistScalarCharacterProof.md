# Scalar real parts of fine twists of unitary data

Author: Worker 510.

`Langlands.Exponents.unitaryFineTwistScalarCharacter.{uF,uV}` proves the
published proposition
`Langlands.Exponents.UnitaryFineTwistScalarCharacterStatement.{uF,uV}`.
The field and representation-carrier universes remain independent.

The implementation obtains the actual full-center character from the published
`Langlands.unitarizableCentralCharacter`. Its restriction `ψ` to the block-scalar
torus has norm one. The homomorphism `f` into the full center is the codomain
restriction of the existing block-scalar map using its proved centrality.
The character `θ` is the block-scalar restriction of the actual real determinant
character with exponent `-v₀`. Set `χ = ψ * θ`.

Coordinatewise continuity of scalar matrices proves continuity of the
block-scalar map, and subtype continuity proves continuity of `f`. The open
kernels of the full-center character and the determinant character pull back
to open kernels of `ψ` and `θ`. Their intersection is an open subgroup contained
in the kernel of `χ`; therefore the latter kernel is open.

The action of the determinant twist is the determinant character times the
original action. Substitute the full-center scalar action and commute the
complex factors to obtain the whole-source scalar action of `χ` on the
flattened Levi. Evaluating `fineTwist` along the forward flattened scalar map
cancels its inverse flattened Levi map. The zero coarse parameter leaves the
same negative fine determinant twist on the original carrier.

Finally the norm-one factor `ψ` disappears from the norm of `χ`. The proved
`T.coe_leviRealPowerCharacter_blockScalar` gives the product of normalized
absolute values to powers `(fine size) * (-v₀)`. Each factor is nonnegative, so
the complex norm of this real product is the product itself. The identity
`d * (-v) = -(d * v)` gives the stated real part. The proof uses no analytic
criterion, Jacquet functor, cuspidality, support or classification theorem.
Its provenance is an internal derivation from the named Library results and
elementary topological and algebraic identities.
