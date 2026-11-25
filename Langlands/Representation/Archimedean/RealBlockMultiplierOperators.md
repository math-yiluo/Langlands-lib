# Parity support and opposite-parameter block operators

This module derives adapters for the explicit real block multipliers
and their actual Frobenius maps. It uses the finite-product formulas, the
proved Fourier parity and uniqueness theorems, and scalar reciprocal identities.
It has no external source.

`RealBlockMultiplier.parityRestrict ε μ` agrees with `μ` when `Even (k-ε)`
and is zero otherwise. The recurrence only compares `k` and `k+2` in the
same parity class; reflection also preserves the class. Restriction therefore
preserves both recurrence and symmetry. Coordinatewise analyticity is preserved
because each coordinate is either the original analytic function or zero.
`parityRestrict_finite` converts a support bound on the parity class to a support
bound at every integer mode.

At the positive exceptional parameter `a_r = ε+2r+1`, for `ε ≥ 0`, the
generic sequence is nonzero exactly at indices `m ≤ r`. Indeed, the numerator
at index `r` is zero, all preceding numerators are nonzero by distinctness
of indices, and all denominators are positive real numbers. For `ε ∈ {0,1}`,
reflection extension gives nonzero generic multiplier exactly at `|k| < a_r`
on its parity class. Its parity restriction vanishes at every mode `|k| ≥ a_r`.
The same restriction turns the existing binomial multiplier's parity-class
finite support into finite support at every integer mode.

`blockFrobMap_eq_of_eq_on_parity` compares Fourier coefficients of two maps
with the same source and target. On the parity class the multipliers agree;
off that class the source coefficients vanish. Compact Fourier uniqueness
then gives equality as actual standard-module maps. Applying this to
`IsBlockFrobData.parityRestrict` proves that parity restriction preserves the
actual Frobenius map on all group points. Thus using the restricted multiplier
does not change a composite operator.

`blockFrobMap_leftInverse` specializes the existing same-block composite
identity to multipliers whose product is one on the parity class.
`RealBlockMultiplierOperators.parameterData` constructs the crossing of two
adjacent characters in any surrounding lists using `genericMultiplier ν ε`
at an arbitrary complex parameter `ν`. Source and target exponents stay fixed:
reflection symmetry suffices for the Frobenius construction.

When `IsGenericParameter ν ε` holds, the scalar identity at opposite parameters
makes the crossing with parameter `-ν` a left inverse. Fourier coefficient
comparison proves the right inverse as well. `parameterEquiv`
packages these two actual maps as an explicit complex linear equivalence.

This module proves inverse identities for single crossings and provides support
adapters. It constructs no parameter limit or normalized four-crossing operator.
For an arbitrary parameter the maps need not intertwine the fixed Lie actions;
no such assertion is made here.
