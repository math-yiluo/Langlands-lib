# Characteristic-zero vector extensions with invariant integration

This internal adapter constructs an actual original-field homomorphic section
for an affine faithfully flat extension `q : E ⟶ H` with a full
finite-dimensional vector kernel over any characteristic-zero field, assuming a
normalized invariant integral on the actual coordinate algebra of the affine
quotient `H`. It preserves the arbitrary universe, the original quotient map,
and the full scheme-theoretic kernel. The vector dimension may be zero.

`InvariantIntegralVectorExtension.exists_extensionSection_of_charZero` uses
`RelativeRoot.IsVectorGroupOfDimension.exists_quotientSection` to obtain a
section as a scheme morphism. The given vector-group hypothesis supplies
coordinates natural on every scheme test. Applied to the actual conjugation
action of `E` on `kernel q`,
`RelativeRoot.isLinearVectorCoordinates_of_charZero` proves scalar linearity
in those coordinates. The kernel inclusion is monomorphic, and equality of its
range with the kernel range is reflexivity. The generic
`InvariantIntegralVectorExtension.extensionSection` construction and its
composition theorem therefore give the required group-scheme section.

`vectorKernelSectionOfInvariantIntegral` chooses such a homomorphism and
`vectorKernelSectionOfInvariantIntegral_comp` proves that its composite with
the supplied `q` is the identity of `H`.

Finally, `characteristicZeroReductiveVectorExtension_of_invariantIntegral`
proves the exact logical implication from
`CharacteristicZeroReductiveInvariantIntegralStatement.{u}` to
`CharacteristicZeroReductiveVectorExtensionStatement.{u}`. Reductivity supplies
affineness of `H`, and the former proposition supplies the integral used above.
The latter is the unchanged Library proposition. This conditional theorem does
not prove invariant-integral existence or the unconditional splitting target.

The provenance is internal: the adapter composes the published affine
vector-torsor section and characteristic-zero linear-action results with the
coordinate-integral defect-averaging construction. The integral-existence
statement has its own source correspondence in its paired Markdown. No Levi
decomposition theorem is used in this adapter or its proof dependencies.
