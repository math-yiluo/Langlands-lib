# Genuine tensor presentations of the actual constant line

This internal construction supports the rank-one clause of
`Langlands.Global.PoleComparison.RelativeIsometryOperationStatement`.
It constructs a tensor presentation of the existing actual constant realization.
It does not yet construct its spherical spectrum or a relative Weil association.

The local factors are trivial representations on `ULift ℂ` in an independently
chosen universe. They are smooth, irreducible and admissible because their
carriers have complex dimension one. Lifted scalar one is a nonzero reference
fixed by every local group. The exceptional set is empty.

`RestrictedTensor.congr` descends the factors to ordinary scalars, and
`RestrictedTensor.scalarEquiv` multiplies the resulting finite tensor entries.
The tensor action is trivial by `RestrictedTensor.map_id`. The explicit
`ConstantFunctions.scalarFiniteEquiv` from `ConstantUnitaryForm` and the existing
equivalence to the actual finite
form image then give `finiteTensorPresentation`. Its form-valued map is
injective and has image exactly the actual constant line.
On elementary tensors, the resulting adelic function is literally constant
with value equal to the product of the descended scalar entries, as proved by
`evaluate_finiteTensorPresentation_pure`.

The construction is derived from the published constant realization and the
published restricted tensor direct limit; it asserts no new literature theorem.
