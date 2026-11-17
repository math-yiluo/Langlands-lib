# All seven Steinberg laws from supplied full roots and a clean Bruhat cover

This internal conditional construction produces actual `SteinbergBigCellData`
from a split pinning, full integral coroot span, a
`SimpleRootCoordinateFamily`, and a Bruhat covering for the actual dynamic
subgroup defined by the polarization of rho. The field is algebraically
closed of prime exponential characteristic. These structural and covering
inputs remain supplied; the construction is not an independent proof of the
unconditional `SteinbergBigCellStatement`.

The generic dominant highest-weight existence theorem supplies a
representation of weight rho. The published conditional geometric adapter
`highestWeightBigCellGeometricData` then supplies the actual diagonalizable
torus map, polarized-rho subgroup inclusion, opposition point, negative-rho
coordinate and extremal coefficient, together with the first six laws. Its
Bruhat covering input remains explicit; no theorem that a regular dynamic
subgroup is Borel, nor an unconditional canonical-rho Borel construction,
is used to supply that input.

The new `suppliedRho_irreduciblePowers` theorem supplies exactly the seventh
law for this same subgroup map and negative-rho coordinate. The elementary
`SteinbergBigCellGeometricData.withIrreduciblePowers` constructor retains all
the geometric witnesses and adds this cofinal whole-space irreducibility
law. Projection lemmas record the original subgroup inclusion, character
coordinate, diagonalizable torus model and opposition point. Every
geometric identity has the unrestricted relative test-scheme semantics of
the seven-law bundle.

The six-law adapter is reused only at its explicit conditional boundary.
Its actual proof closure was checked separately from unconditional Borel and
root-existence assembly. The new seventh-law proof uses supplied-family
normalizer transport, full root-word polynomial charts, Frobenius upper and
lower bounds, and coefficient-space transport. No structural premise is
discharged by this definition. This is derived internal content and adds no
external source assertion.
