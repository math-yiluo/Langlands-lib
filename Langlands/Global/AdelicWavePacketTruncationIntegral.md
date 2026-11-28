# Arthur truncation of compact spectral integrals

`WavePacketTruncationIntegralStatement` applies to a jointly continuous family on a real spectral coordinate space and the full adelic group. Each spectral member is left rational invariant, and the family vanishes outside one compact spectral set. Truncation gives a jointly measurable family, continuous in the spectral variable at every fixed adelic point. Its spectral integral agrees pointwise with the truncation of the original integral.

For each standard unipotent radical, rational invariance descends the constant-term integrand to the product with the compact unipotent quotient. Its joint continuity follows from the open quotient map. Restricted to the compact spectral set and that quotient, the integrand is integrable for the product measure, so Fubini interchanges the two integrals. The constant term vanishes outside the original spectral support. For each adelic argument, `truncationFiniteness` bounds the active rational cosets by a finite set independent of the spectral variable. Integration commutes with both finite sums.

To prove joint measurability, `wavePacketTruncationIntegral` factors each coset summand into a continuous constant term and a measurable cutoff. The cutoff is `cutoffKernel` applied to the constant function \(1\), since the normalized radical quotient has mass \(1\). The countable coset sums and the finite parabolic sum preserve measurability.

This is the interchange of truncation and spectral integration in E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*, §8, printed p.328 (volume PDF p.337), `lapid-2011-asymptotic-inner-product-truncated-eisenstein`, SHA-256 `760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`.
