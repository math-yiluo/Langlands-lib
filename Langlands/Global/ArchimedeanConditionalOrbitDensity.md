# Compact and enveloping orbit density from explicit analytic inputs

Worker 94 assembles an internal conditional proof of the exact published
`CompactLieOrbitDensityStatement K n`. The two assumptions are explicitly
`JointFiniteAnalyticityStatement K n` and
`CompactComponentCoverageStatement K n`. Neither is inferred from an
unproved statement declaration. The companion
`ArchimedeanCompactLieOrbitDensityProof` instantiates both assumptions with
published proofs. The scalar orbit construction is imported from its
published module, which retains its original authorship. This helper
does not prove automorphic growth.

For a continuous complex linear functional annihilating the span of all
actual vectors `R(k)D(a)f`, the implemented scalar coefficient is
`F(g) = ell(R(g)f)`. The previously constructed genuine intertwiner sends
the finite joint orbit of `f` to the finite joint orbit of `F`, so the
explicit analytic input applies. The actual enveloping derivative identity
makes every enveloping derivative of `F` vanish at each compact point `k`.
The published enveloping zero jet and analytic matrix jet uniqueness
proofs then make `F` vanish throughout the component of `k`. The explicit
component coverage input places any requested group point in such a
component.

The continuous complex annihilator criterion therefore places each
`R(g)f` in the closure of the displayed span, with the full published
derivative topology. The argument keeps every number-field universe and
every natural rank. It makes no connectedness assumption and proves
neither finite dimensionality of that span nor reproduction.
