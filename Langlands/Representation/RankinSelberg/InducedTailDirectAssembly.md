# Conditional direct-rank tail-divisibility assembly

Implementation and proof explanation: Worker 53. Preparation and validation
for this contribution: Worker 356.

The helper `inducedTailDirectPolynomialDivisibility_of_spans` assumes
`InducedTailSpanStatement` and supplied certified polynomials for the actual
full and tail pairs in `InducedTailLFactorStatement`. For test rank strictly
below the full induced rank, it proves `Ptail ∣ Pfull`. This support module
proves neither the span comparisons nor factor existence.

The proof reads the full symmetric certificate in its larger-first branch,
selects one compatible quotient measure from that certificate, and extracts
the normalized generator for its zero-row block. It splits by the test index
relative to the tail index. In each case it selects an independent compatible
tail measure from the corresponding certificate, extracts its generator, and
applies the corresponding assumed span clause. In the equal case substitution
of the equal rank indices removes the test-action transport. In the
intermediate case the tail certificate is read in its reversed-rank branch,
with the same canonical additive character as the span statement.

The published `normalizedGeneratorSpanDivisibility` converts each inclusion
to ordinary polynomial divisibility. Its normalization argument removes the
possible power of `X`. The quotient measures are selected independently,
even when their ranks agree. The supplied self-dual additive measure and its
rectangular product measures are retained. The field and all three original
representation carriers have independent universes. The full induction uses
exactly the two explicit `ULift`-conjugated actions, `Shahidi.twoBlocks`, and
`Shahidi.pairFamily` of the parent.

Provenance is internal assembly of the published
[span interface](InducedTailSpanStatement.md) and
[Laurent divisibility proof](LaurentDivisibilityProof.md).
Their original analytic source interpretations remain unchanged. This module
is used by the separate
[conditional assembly proof](InducedTailConditionalAssemblyProof.md), which
still assumes every analytic premise and does not prove the closed parent.
