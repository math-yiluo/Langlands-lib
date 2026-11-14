# Actual reflected first-block integrands

Derived infrastructure for JPSS (1983), Section 4.9, printed pages 416–418,
and Section 4.10(2), printed page 419 (`jpss-1983-rankin-selberg`).

The actual smaller dual JPSS integrand is evaluated at the quotient reflection
`[v] ↦ [w_a v^ι]`. Expanding its two actual Whittaker dual transforms and the
right translations gives the lower test matrix already proved by matrix
transport. The second dual transform returns the original first-block
coefficient by involutivity. The determinant absolute value is inverted;
positivity of its real value justifies the complex inverse power identity.
No integrability follows from this pointwise identity.

## All-field port

The declarations of this module that involve the p-adic field and that the Library's proofs of JPSS (3.1) multiplicativity use are re-declared over every nonarchimedean local field, of any characteristic, in `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockReflectionIntegrands` (the Markdown there lists them). For those declarations this p-adic module is superseded by the all-field port; its Lean code is unchanged.
