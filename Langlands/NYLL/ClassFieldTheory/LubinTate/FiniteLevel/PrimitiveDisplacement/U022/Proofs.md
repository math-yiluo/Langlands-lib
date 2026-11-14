# Exact principal-depth proof

This proof adapts NYLL source unit M362.022, from
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveDisplacement.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, retaining the original
copyright, authorship and Apache-2.0 notice. Its exact target is
`Langlands.NYLL.PortInternal.M362.d022Statement`, imported from the
shared `PrincipalDepth.Statements` module. The theorem retains both source
universes and the full source argument order.

The proof unfolds concrete principal-unit membership and uses
`Valuation.IsUniformizer.is_generator` to identify the maximal ideal with
`Ideal.span {π}`. Mathlib's `Ideal.span_singleton_pow` and
`Ideal.mem_span_singleton` turn membership in its `k`th power into
uniformizer-power divisibility. The resulting quotient cannot be in the
maximal ideal, since ideal multiplication would give membership at `k + 1`.
`IsLocalRing.notMem_maximalIdeal` makes the quotient a unit. This follows the
source's factorization argument while directly using Mathlib APIs instead
of NYLL's intermediate uniformizer-divisibility wrappers.

Source passage: `PrimitiveDisplacement.lean:405–446`; ambient context
lines 33–43. Source file SHA-256:
`520ab08231608ac43915d72c8a94c5d4ea1ad2fd4b7311a77f8f889a37421cbc`.
The exact target is accepted artifact
`50e77c8e-8514-41dd-833a-56e2df3fb07e`, published in Library commit
`b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a`. This proof imports the public
target pair unchanged. Source registration is
`nyll-classfieldtheory-fbd320cd-supplement`.
