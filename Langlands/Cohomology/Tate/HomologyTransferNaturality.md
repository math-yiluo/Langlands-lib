# Naturality and connecting maps for homological transfer

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation.

The ordinary transfer chain map is natural in its coefficient representation.
The proof evaluates both composites on inhomogeneous generators, applies the
explicit coset formula, and uses equivariance of the coefficient morphism in
each summand. In chain degree zero its formula is exactly the inverse-coset
sum.

The chain map extends from the actual Tate complex to the auxiliary complex
with zero splice differential. This extension has the independently constructed
ordinary transfer as its negative-degree component and zero as its
nonnegative-degree component. It is used only to compare existing cohomology
groups. Naturality gives a morphism of short exact sequences of complexes,
so Mathlib's homology-sequence naturality proves compatibility with their actual
connecting morphisms. On Tate degree minus one, a norm-zero representative
maps to the ordinary zero-chain class of its inverse-coset sum.

These are internal comparison certificates based on the proved chain
construction in `HomologyTransfer` and the representative formulas in
`HomologyTransferRepresentatives`. The use of the zero splice follows the
existing `ChainComparison` module. It does not redefine Tate cohomology,
assume the comparison, or require finite-dimensional coefficients.

The underlying ordinary transfer is as in Serre, *Local Fields*, Greenberg
translation, GTM 67 (1979), Chapter VII section 7, printed pages 118–119
(PDF pages 124–125), and Chapter VIII sections 1–2, printed pages 127–130
(PDF pages 133–136). Registered source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
