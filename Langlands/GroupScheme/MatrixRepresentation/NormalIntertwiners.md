# Linear operations and normal-subgroup conjugation of actual intertwiners

`intertwinerSubmodule ρ σ` is the ground-field submodule of matrices intertwining
two actual group-scheme representations on every affine test. The module proves
closure under zero, addition, scalar multiplication and finite sums.

`Intertwines.normalConjugate` takes an actual monomorphic subgroup inclusion
`i : H ⟶ G` with all-test normal range. If `C` intertwines the restrictions of
`ρ` and `σ` to `H`, then for every rational ambient point `g`, the matrix
`σ(g) C ρ(g⁻¹)` still intertwines those restrictions on every test algebra.
The actual normal-subgroup inner automorphism converts the given intertwining
identity into its conjugate. Multiplication by the ambient matrices and their
inverses recovers the desired identity. No smoothness, reducedness, finite-type
or characteristic hypothesis on either group is needed.

`Intertwines.normalConjugate_sum` proves the same assertion for every finite
linear combination of these rational conjugates. Thus normalized averaging over
an ordinary finite component quotient preserves actual identity-component
equivariance, even though rational-point equivariance alone would not detect
nilpotent test points.

## Provenance

This is internal derived infrastructure for the averaging argument underlying
Milne, *Algebraic Groups* (2022 corrected reprint), Exercise 4-3, printed p.97
(PDF p.108), read in the registered original `milne-2022-algebraic-groups`,
SHA-256 `f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
The full registered official errata snapshot
`milne-2022-algebraic-groups-errata-2026-11-04` has no entry for that exercise.

The implemented proof derives from the public actual `normalInnerIso` and its
point formula in `MatrixRepresentation.NormalCharacterSpan`, the constant-point
matrix formula, and elementary matrix associativity and inverse identities.
It does not assert rational-point density, construct a finite scheme quotient,
or prove the connected multiplicative-type classification.
