# Convolution equations under a finite change of Iwasawa compact

`Langlands.Global.HarishChandraFiniteCompactTransportStatement` compares
two maximal compact subgroups that give Iwasawa coverage for the same
parabolic and have the same infinite projection. Let the nonzero
values of each kernel be supported over the intersection of the two
finite projections. A pointwise uniform convolution equation for the
twists constructed from either compact then holds for the twists from
the other with the same kernels and scalar coefficients.

`height_sub_mul_eq_of_finite_mem` uses the height comparison in
`AdelicEisensteinFiniteCompactChangeProof`. The difference of the
heights depends only on the finite point. For a translation whose
finite coordinate is in the intersection, replace the translating
element by its pure finite component. That element lies in both
compacts, so right invariance of each height gives equality of the
height difference before and after translation.

The two twists differ pointwise by the exponential of the pairing
with this height difference. The exponential factor is constant on
the right translates used in each convolution integral and factors
out of it. It also multiplies the right-hand side of the equation.
The argument preserves the chosen scalar functions at every parameter.

This is a derived comparison for the equation of Bernstein–Lapid,
*On the meromorphic continuation of Eisenstein series*, §8.3,
Lemma 8.3, p. 223
(`bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`).
