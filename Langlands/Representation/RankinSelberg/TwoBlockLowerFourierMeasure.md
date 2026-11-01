# Exact compatible-measure transport for lower duality

This helper develops the measure change of variables for JPSS Section 4.8(4),
printed p.415, on the actual Section 4.7(1) lower quotients. The uniform
compatible-measure and determinant-slice formulation is derived packaging.

The original source is Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg Convolutions* (1983), registered as `jpss-1983-rankin-selberg`, SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`. Section 4.7 has (1)–(5); the first-block formula (8) belongs to Section 4.9, p.418, outside this module.

The supplied standard quotient measure is transported by the inverse actual
`lowerToStandard` map; `lowerQuotientMeasure` is exactly this map measure.
The reflected inverse-transpose automorphism of the general linear group and
its restriction to the upper-unipotent subgroup are involutions. Their Haar
moduli are positive, square to one, and hence equal one. The published
`IsCompatible.map_quotientAutomorphism` formula therefore has scalar one.
Right invariance of the same compatible quotient measure supplies the final
Weyl translation. Conjugation through the two actual lower-to-standard maps
proves preservation of both transported measures; the measurable equivalence
gives inverse preservation. Restriction along the proved slice preimages
supplies both exact restricted-measure laws.

The canonical p-adic specialization retains every supplied right-invariance
certificate on the exact `unipotentHaar` and every compatible measure for the
exact `generalLinearHaar` and `unipotentHaar`. It neither chooses another
normalization nor assumes invariance under duality. It asserts no existence
of a compatible measure, Fourier identity, coefficient identity or convergence.
