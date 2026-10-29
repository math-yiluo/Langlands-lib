# Conditional intermediate-tail span assembly

Worker 318 and Worker 829 implement
`inducedTailIntermediateDiagonalExtensionSpan`, whose type is exactly
`InducedTailIntermediateDiagonalExtensionSpanStatement` with independent
field, full-representation and test-representation universes.

The proof closure consists of this module and the paired helper modules
`InducedTailIntermediateLocalization`, `InducedTailIntermediateComparison`,
`InducedTailIntermediateIntegrands`, `InducedTailIntermediatePointwise`,
`InducedTailIntermediateIntegralAssembly`,
`InducedTailIntermediateQuotientPointwise` and
`InducedTailIntermediateQuotientAssembly`. It imports the published
`InducedTailIntermediateCoefficientAdapters` and
`InducedTailIntermediateQuotientData` pairs unchanged.

The final wrapper applies
`InducedTailIntermediate.mem_full_zetaSpan_of_diagonal_extension`. The chart
and density bound locally in the statement reduce to the actual
`quotientChart` and `quotientDensity` definitions used by the implementation.
Both charts compose the published lower-block quotient chart with the same
numerical-rank congruence, and both densities are the same negative integer
power of the actual quotient determinant absolute value.

The helper proof first obtains compact open additive and multiplicative
localizers and an actual full coefficient from
`exists_localized_quotient_integrand_comparison`. This uses the supplied
diagonal extensions, published Whittaker localization and last-row cutoff,
smoothness of the actual test coefficient, and the pointwise determinant
weight calculation. Quotient induction lifts the representative identity
to every small quotient point. The two parameter indicators occur pointwise,
including off their supports; the density remains explicit.

The full coefficient and representation are transported only along the
displayed numerical rank equality. Actual coefficient-image membership and
smoothness are preserved. The published zero-row continuity theorem makes
the full integrand Borel measurable, so the retained measure-transfer premise
applies. The canonical p-adic field is second countable, which makes the
matrix product measurable structure Borel and the open localizers measurable.
The quotient density is measurable and finite everywhere.

Worker 829's `mem_zetaSpan_of_localized_disintegration` then combines that
transfer with the weighted pointwise equality. Moving the finite density
into the integrand reduces absolute integrability and the integral to a
product with the two indicators. Product integration yields the original
tail integral multiplied by `C` and the real volumes of both localizers.
Their compactness gives finite volumes; their openness and their subgroup
identity elements give positive volumes. Thus the scalar is nonzero.
Half-plane integrability and rational continuation transfer to the actual
full zero-row integral after multiplication by this constant. The full
value belongs to the actual zeta-value set, and multiplying by the inverse
constant in the Laurent span removes that factor.

The proof retains every premise of the statement. It does not construct the
diagonal extension or prove full Whittaker type or quotient disintegration.
It also does not transport the reversed tail character to the canonical
same-character tail, or prove the unchanged four-universe closed
intermediate-rank span statement. Provenance is the internal composition of
the named Library constructions and the paired helper proofs listed above.
