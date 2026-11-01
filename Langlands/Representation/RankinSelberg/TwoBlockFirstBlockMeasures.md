# Restriction-normalized measures for the first-block quotient

Author: Worker 27.

This module supplies internal measure prerequisites for the normalized
first-block formula of JPSS (1983), Section 4.6, printed page 412, equation (6).
It does not prove that formula or any disintegration identity.

For the canonical topology of a p-adic field, `normOneHaar F n` is the pullback
of `generalLinearHaar F.Carrier n` along the inclusion of the open subgroup
`normOneSubgroup F (n + 1)`. Mathlib's open-embedding pullback results prove
that it is Haar and regular. Its measurable-embedding pullback result proves
right invariance. `map_normOneHaar` identifies its pushforward with the exact
restriction of the ambient measure. This fixes the normalization without an
additional scalar.

The mixed measure `mixedHaar F h` transports the product of this measure and
the second block's published `unipotentHaar` through the actual
`mixedSubgroupEquiv`. The corresponding continuous multiplicative
equivalence proves the Haar property. Regularity follows from regular Haar
measure on the locally compact product and transport by the homeomorphism.
The proof of right invariance transports right multiplication through the
multiplicative equivalence. The published closed-subgroup compatible-measure
existence theorem then applies to the mixed subgroup and the fixed ambient
general linear measure.

These constructions and proofs are derived prerequisites: JPSS give no
explicit measure normalization in equation (6). The normalization matches
`TwoBlockFirstBlockQuotientIntegrationStatement`; the current module proves
only the subgroup measure and existence assertions described above.

Source context: H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg convolutions* (1983), registered as
`jpss-1983-rankin-selberg`, printed page 412, displays (5) and (6), visually
read from one-based PDF page 47. The source file has SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
