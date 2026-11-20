# Holomorphic dependence of compact real Godement sections

`RealGodementSectionAnalyticStatement` fixes a real parity, a continuous lower function, a continuous rectangular test with compact full-row-rank support, and an upper translating matrix. For a lower-rank Borel measure finite on compact sets, the value of the Godement section is entire in the new leading exponent.

The proof writes each determinant character as its value at exponent zero times the exponential of the exponent times the logarithm of the absolute determinant. Compact full-row-rank support confines the lower group variable to a compact subset of the invertible matrices. The section kernel at exponent zero is continuous and compactly supported there. Multiplication by every real exponential weight is integrable, so the Library's exponential-integral holomorphy theorem gives differentiability everywhere in the exponent. The outside determinant weight is entire and the kernel identity gives the asserted section value.

This implements the fixed-parity, fixed-lower-vector analytic dependence used for the Godement sections in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §7.1 and §7.2, pp. 46–48. It supplies pointwise entire section entries for the compact-type continuation argument.
