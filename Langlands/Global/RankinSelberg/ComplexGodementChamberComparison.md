# The compact Godement comparison in the Jacquet chamber

`integrable_jointKernel_of_chamber` proves the joint absolute
integrability required for the open-cell comparison. The compact
rectangular test is continuous and supported in the full-row-rank
locus. The larger inducing list starts with the added character,
and its real exponents strictly decrease.

The proof takes the norms of the inducing characters and the test.
`absoluteCharacter` has weight zero and exponent the real part
of the given exponent. The corresponding spherical section for the
smaller list bounds the smaller-rank input by Iwasawa decomposition
and a compact bound. The Godement integral for the norm of the test
and this spherical section gives a continuous section with the
larger Borel transformation law and a nonnegative real integrand.

The chamber convergence theorem makes that section integrable along
the larger unipotent group. In the split unipotent coordinates the
determinant prefactor is constant and nonzero. Positivity identifies
the norm of the inner Godement integral with the integral of the
norms, so Tonelli gives absolute integrability of the positive joint
kernel. It dominates the original Jacquet kernel up to the compact
bound, since the integrating character has unit modulus.

`complexGodementChamberComparison` applies the checked Fubini
comparison with the actual entry Haar measure in both ranks. It
proves (7.6) for these tests in Jacquet, *Archimedean Rankin–Selberg
integrals* (2009), §7.2, pp. 47–48, including the upper-Borel
Weyl determinant factor. The compact test class is used in the
spanning argument of §7.1, pp. 46–47.
