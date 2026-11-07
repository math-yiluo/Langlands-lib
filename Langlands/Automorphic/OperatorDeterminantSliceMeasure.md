# Support and covering-set estimates for the determinant-band measure

This internal construction supplies the actual measure and a conditional
square-integrability bridge for the determinant-band pairing. It does not derive
the covering-set estimate from cuspidality or prove the final local-unitarity
statement.

For a second-countable topological group `H` with its Borel measurable structure,
a discrete subgroup `Γ`, and a left-invariant measure `ν`,
`LeftCosetSpace.isOpenPosMeasure_discreteQuotientMeasure` proves that the existing
fundamental-domain quotient measure has full support when `ν` has full support
and open sets of the quotient are measurable. If a nonempty open quotient set
had zero measure, its invariant preimage would have zero measure by the
fundamental-domain identity. That preimage is nonempty and open, contradicting
full support of `ν`.

`LeftCosetSpace.lintegral_restrict_discreteQuotientMeasure_le` assumes that `A` is
a measurable quotient set and `t` is a measurable subset of `H` meeting every
orbit above `A`: for each representative `x` over `A`, some `γ : Γ` satisfies
`γ * x ∈ t`. For every measurable nonnegative extended-real quotient function
`f`, it proves

`∫⁻ q in A, f(q) ≤ ∫⁻ x in t, f([x])`.

Pointwise, the indicator of `A` times `f` is bounded by the orbit sum of the
indicator of `t` times the lifted function. Integration over the fixed
fundamental domain, interchange with the countable nonnegative sum, and the
existing fundamental-domain integral identity give the inequality. The
covering set need not be a fundamental domain, and the argument needs neither
right invariance nor finite volume.

For an arbitrary-universe number field `F` and natural rank `n`,
`OperatorDeterminantSlice.quotientHaarMeasure` is the existing rational quotient
Haar measure of the actual matrix general-linear group scheme, using its proved
affine and smooth instances. Its full-support instance follows from the preceding
lemma and the actual ambient Haar measure. `matrixHaarMeasure` is the pushforward
of that same ambient Haar measure through the existing adelic matrix group
homeomorphism. It is a Haar measure for any Borel measurable structure on the
original `AdelicGL F n`. This construction fixes the normalization used in the
comparison; it does not identify it with a separately chosen matrix Haar measure.

For an unchanged `OperatorRealization F n`,
`lintegral_band_le_cover` specializes the inequality to its original continuous
quotient function's squared extended norm. The hypothesis is a measurable
matrix set `t` such that every matrix with real determinant norm in the closed
interval `[1,2]` has a rational left translate in `t`. The quotient integral over
the strict band `(1,2)` is bounded by the original realized function's squared
extended-norm integral over `t` with respect to `matrixHaarMeasure`. The
matrix/group-scheme homeomorphism preserves the principal rational maps, so the
covering property transports to the actual subgroup quotient. The pushforward
integral identity then compares the exact original functions.

`memLp_band_of_cover` concludes `MemLp` at exponent `2` on the band when that
covering-set integral is finite. Continuity supplies measurability, and the
finite squared extended-norm integral is the standard `L²` membership criterion.
No central character or positive-rank hypothesis is needed for this measure
bridge. Right invariance and the unconditional cuspidal covering estimate remain
separate obligations.

The provenance is internal: these are deductions from the Library's discrete
quotient and actual adelic Haar constructions, the preceding determinant-band
geometry and pairing interfaces, and Mathlib's nonnegative integral and `MemLp`
identities. They make no additional original-literature claim.
