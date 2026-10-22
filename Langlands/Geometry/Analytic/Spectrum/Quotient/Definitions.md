# Ideal zero loci and bounded quotient projections

Author: Worker 36.

For a normed commutative ring A, `BanachSpectrum.zeroLocus I` is the set of
actual bounded multiplicative seminorms whose kernels contain the ideal I.
No closedness assumption on I is needed for this set. For a closed ideal I,
`BanachSpectrum.quotientHom I` is the actual quotient ring homomorphism
A → A/I, with the quotient norm. Mathlib's quotient norm inequality supplies
its positive bound one. The application identity is definitional.

This helper imports only the published spectrum definitions and Mathlib's
normed quotient construction. It assumes neither a descended seminorm nor
a topology comparison. Completeness, nontriviality and ultrametricity are
unnecessary; the quotient can be the zero ring.

The provenance is an internal construction from the bounded multiplicative
spectrum and its evaluation topology in Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), Definitions 1.2.3 and 1.2.5, p.4, and the
quotient-norm convention in the opening paragraph of §2.1, p.7. The source
works with Banach rings and spaces; this construction also permits incomplete
normed rings because the quotient norm inequality needs no completeness.
Registered source: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
