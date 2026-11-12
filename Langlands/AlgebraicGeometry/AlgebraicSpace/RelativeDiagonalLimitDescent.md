# Separatedness descent from a fixed relative-diagonal chart

This internal development restricts the represented relative-diagonal square
of `RelativeDiagonalCharts` along a scheme base change. Naturality of the
scheme Yoneda base-change isomorphism identifies its scheme map with the
actual slice pullback of the original comparison. A factor-exchange
isomorphism identifies that slice pullback with the scheme-limit convention.

As a result, separatedness after base change is detected by the closed
immersion property of the base change of one fixed scheme map. The conditional
limit theorem applies the published `relativeClosedImmersionDescent` theorem
to this scheme map on the cofiltered category of arrows to the original
stage. Its scheme finiteness hypotheses are explicit.

The final theorem `spaceLimitSeparatedDescent` discharges these hypotheses for
the exact published limit statement. Choose an affine source atlas locally
of finite presentation over the original affine stage. Its kernel pair over
the source space is locally of finite presentation by an étale projection.
The two kernel pairs are compact by the quasi-compact diagonals of the two
spaces. Each is separated over the base because its pairing into the affine
product of the chart scheme with itself is a monomorphism. This monomorphism
argument adapts the relation finiteness proof in Worker 116's
`FinitePresentationEtaleAtlas` development. The comparison is then locally of
finite type, quasi-compact and quasi-separated, and its target is
quasi-compact over the base, exactly as the scheme theorem requires.

This proves the full separatedness clause of
`SpaceLimitPropertyDescentStatement`; the other seven clauses remain separate.
