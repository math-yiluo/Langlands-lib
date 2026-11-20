# The real two-block parabolic integration formula

`Langlands.Archimedean.realBlockParabolicIntegration` proves
`Langlands.Archimedean.RealBlockParabolicIntegrationStatement` by specializing
`realLeviParabolicIntegration` to the block sizes `![a, k]`. The positive constant
comes from the general theorem. [General real parabolic integration](RealLeviParabolicIntegration.md)

In the two-block chart, a lower-unipotent coordinate has its row in the second
block and its column in the first. The proof identifies these coordinates with
`Fin k × Fin a`. Uncurrying the rectangular functions and reindexing by this
equivalence preserve Lebesgue measure. After the rank is identified with `a + k`,
entrywise comparison gives the lower-unipotent matrix and the block-diagonal
matrix in the target. This transfers the general theorem's section integrability
to every pair in `O(a) × O(k)`.

For Fubini, the proof uses continuity of the joint integrand in the compact and
unipotent variables. Its norm is bounded by a constant times the integrable
product of inverse Gram determinants from `RealLeviTwoBlock`. The bound is
independent of the compact variables, which have total measure one. Thus the
integral over the unipotent coordinates is integrable over the compact factors.
The measurable equivalence `MeasurableEquiv.piFinTwo` takes the dependent product
of the two Haar probabilities to their binary product. Fubini gives the
iterated integral with `O(a)` on the outside and `O(k)` on the inside.
[Gram bound and integrability](RealLeviTwoBlock.md)

The coordinate equivalence and the measure comparisons also apply when either
block size is zero.
