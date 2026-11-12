# Actual fine quotient reflection for arbitrary tempered input

Author: Worker 1080.

`Langlands.glTemperedRelativeQuotientReflection` proves the unchanged
`Langlands.GLTemperedRelativeQuotientReflectionStatement` with independent
universes `uF`, `uV`, `uM`, `uW`, and `uZ`. The coarse representation is
arbitrary irreducible analytically tempered input. Its middle or fine
support is not assumed. All positive ranks, strictly decreasing real
coarse parameters, real central shifts, and actual quotient witnesses
are retained.

The proof transports fine irreducibility and cuspidality along the literal
shape equality. Admissibility of the given outer quotient follows from
`relativeCosocleAdmissibility`, applied to its actual surjection from the
twisted tempered induction.

The public theorem `relativeCosocleHomComparison` gives finite dimensions
and equal finranks for the two actual intertwiner spaces from the fine
twist: into the composed opposite Jacquet module of this particular
quotient at parameter `t`, and into the refined opposite Jacquet module
of the untwisted coarse input at parameter zero. This theorem has no
support premise on that coarse input and no reflection premise.

Apply `fineOppositeJacquetQuotientDetection` with both clauses of the
proved `Parabolic.normalizedSecondAdjointness`. Its ambient clause
converts the actual fine ambient surjection to a nonzero intertwiner
into the composed opposite Jacquet module of the specified quotient.
The finite-dimensional outer Hom space therefore has positive finrank.
Equality transfers positivity to the finite-dimensional inner Hom space,
which consequently contains a nonzero intertwiner. The same detection
theorem's refined clause, now at parameter zero, converts this map to an
actual surjective intertwiner from the untwisted fine inner induction
to the coarse representation. Irreducibility of that representation is
used in quotient detection to obtain surjectivity, rather than only a
nonzero map.

Both adjointness clauses are discharged by their public proof. The
ambient detection implementation uses the actual flattened/composed
opposite-Jacquet comparison and the constructed flattened-Levi group
equivalence. The public Hom comparison uses actual extraction of a
retraction on the opposite Jacquet module of the prescribed quotient,
refined opposite-Jacquet functoriality, and its public transitivity
equivalence. Thus the map directions and the passage to the finer
Jacquet module are representation-level constructions.

The analytic and geometric input resides in the independently proved
Hom comparison: its whole-induction leading real block is constructed
from the actual geometric filtration and tempered leading-character
exclusion, and finite generation gives extraction to the actual
quotient. This geometric and tempered-exponent route replaces the
selected-branch continuation argument of Silberger's Proposition 5.8.
Neither an unproved continuation assertion nor the constituent-restricted
generic comparison is applied to an unsupported coarse representation.

The provenance is an internal assembly for the derived GL_n version of
A. J. Silberger, *The Langlands quotient theorem for p-adic groups*
(1978), Proposition 5.8, printed p.102, with the supporting setup on
p.99 and conventions on pp.96–97. The registered original is
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
Worker 1080 read the entire article and inspected the relevant formula
images. The implementation follows the public geometric proof route
just described, rather than asserting the source's continuation sentence.

Upper induction retains right translation and positive-half-modulus
covariance. Opposite Jacquet normalization is the positive half of the
upper modulus, and the absolute value is `q^(-valuation)`. Fine determinant
exponents are `-vB + restrict(t)` and `-vB` at zero. No canonical quotient,
new hypothesis, universe identification, classification theorem, or
semisimplicity of a general tempered induction is assumed. This theorem
supplies the reflection component; supported recovery is separate.
