# Actual two-block radical fiber kernel

Author: Worker 113. This is internal derived infrastructure for the unchanged
normalized two-block quotient integration statement.

The affine change `unipotentShift` preserves the supplied rectangular additive
Haar measure: its linear part is `rectangularConj` of two unipotent diagonal
blocks, whose determinant norms are one; its translation also preserves Haar.
The published fiber-point identity then makes the pushforward fiber measures
invariant under changing representatives by the full unipotent subgroup.

The map to fiber measures is measurable by joint continuity of `fiberPoint`,
measurability of parametrized pushforwards under an s-finite source measure,
and standard Borel descent on the actual left quotient. `fiberKernel` descends
that measure-valued function, and `fiberKernel_mk` is its exact representative
formula. The supplied additive Haar is unchanged.

This module constructs the measurable kernel. Compact finiteness,
s-finiteness and its normalized quotient measure tower are separate obligations.
