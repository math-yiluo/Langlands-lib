# Actual lower Fourier specialization and scalar transport

The inverse-character test uses the published `firstDualFunction` directly.
Its representative formula is `W(w inverseTranspose(g))`, with actual character
`psi.scale (-1)`. The proved block rotation cancellation uses `dual_rotation`
and introduces no measure, section, functional or nonvanishing assumption.

This derived helper specializes the published arbitrary-row Fourier companion
identity to the actual lower partial sections, retaining the supplied self-dual
additive Haar measure and the actual Fourier pair. Reversal exchanges the source
rows zeta and eta, and the dimension equality is transported through the actual
contiguous placement. The resulting factor is exactly the canonical normalized
absolute value of the determinant.

The abstract scalar transport lemma proves integrability equivalence under a
measure preserving measurable equivalence and a positive almost everywhere
constant scalar comparison. It also proves both the complex integral and real
norm integral identities for total Bochner integrals. It imposes no integrability
hypothesis.

The original source for the Fourier identity is Jacquet–Piatetski-Shapiro–Shalika,
*Rankin–Selberg Convolutions* (1983), registered as
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
Section 4.8(2)–(4), printed p.415, with the lower rows and subgroup of
Section 4.7(1), pp.412–414. Section 4.7 has (1)–(5); the first-block formula
(8) is Section 4.9, p.418, outside this module. The scalar transport lemma is
internal measure-theoretic packaging, not a literal source theorem.

The implemented row proof first reverses the indicator rows, then multiplies
the published row theorem by the nonzero determinant absolute value. Explicit
contiguous joins identify its row coordinates. Character scaling by minus one
and the two reversed block indices give `partialSection_fourier`.

This focused helper module supplies the test function, pure Fourier
specialization and abstract scalar transport only. It does not yet assert the
actual integrand or determinant-slice coefficient comparison.
