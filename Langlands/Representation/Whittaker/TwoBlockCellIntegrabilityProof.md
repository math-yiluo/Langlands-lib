# Scalar Jacquet integrability for cell vectors

`Langlands.Whittaker.twoBlockCellJacquetIntegrability` proves
`TwoBlockCellJacquetIntegrabilityStatement` for the actual ordered canonical
normalized induction and its compactly supported cell submodule.

The proof installs the canonical p-adic topology and Borel structure.
`Induction.eval_isLocallyConstant` gives local constancy of each smooth induced
function. Postcomposing with the algebraic scalar linear functional preserves
local constancy, without requiring a topology on the inducing tensor carrier.
The cell representative is continuous, being a fixed Weyl matrix times the
continuous exchanged-radical map. Composing with it makes the scalar restriction
locally constant and hence continuous.

The submodule condition supplies compact support of the tensor-valued cell
restriction. The scalar linear functional maps zero to zero, so postcomposition
preserves compact support. Multiplication by the continuous Jacquet kernel
also preserves compact support. The resulting scalar product is precisely
`Shahidi.jacquetIntegrand`. The proof concludes with
`Continuous.integrable_of_hasCompactSupport`, for the given measure finite on
compact sets.

This is an internal consequence of the published smooth-induction,
cell-restriction and scalar-integrand definitions. It uses only compact support
of the restriction, without using the support-in-the-cell condition.
It proves no unipotent stability, scalar covariance or extension theorem.
