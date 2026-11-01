# Principal right averages for uniform box extraction

This internal auxiliary module develops normalized right averaging, a compact
principal averaging measure, and extraction of the original matrix integral.
It does not prove the matrix functional equation comparison.

The general right averaging identity uses right Haar invariance through the
measure preserving shear `(k,g) ↦ (k,gk)`. A product integrability argument and
Fubini prove actual convergence of the averaged weighted integral and its value.
The weight is assumed right invariant under the averaging set. Dividing by its
finite nonzero mass preserves the original integral.

For a measurable subgroup the change of integration variable `x ↦ kx` proves right
invariance of the average. An already right fixed function is unchanged.
Continuity follows from integration of a continuous function over the compact
principal subgroup. Left Whittaker equivariance is preserved pointwise.

The fixed box has upper row levels `A=q+a` and `q`, with principal level `a`.
The published box arithmetic proves right invariance on all matrices. Thus a
convergent original box integral remains convergent after right averaging, with
the same value. UniformBox then extracts the averaged restriction to GL1, for
any additive conductor and every continuous left equivariant function.

For every canonical p-adic field, every natural index `n`, principal level `a`,
and real scalar `C`, `principalAveragingMeasure` is the finite positive measure
`ofReal(C / h.real(K)) • h.restrict K`, where `h` is the existing normalized GL
Haar measure and `K` is the actual principal subgroup of GL_(n+1). Its Haar mass
is strictly positive and finite. If `C ≥ 0`, the measure has total mass
`ofReal C`, and for any complex function `H` its totalized right integral equals
`C` times `principalAverage`. The measure is concentrated on the compact
principal subgroup. Its determinant has normalized absolute value one almost
everywhere; no assertion that its determinant is literally one is made.
Every continuous translate is actually integrable against this measure.
For a right principal fixed original function, its integral is exactly `C H(g)`.

In `principalMeasure_extraction`, the ambient group is GL_(m+2), for every
`m ≥ 0`. The character is arbitrary. Let `c` be its actual additive conductor,
choose `a > 0` with `c+a ≥ 0`, and let `C` be UniformBox's strictly positive
`boxExtractionConstant` for levels `(c+a,c,a)`. For every continuous
left standard character equivariant `H`, genuine convergence of the original
box matrix integrand implies genuine convergence of the scalar function
`g ↦ ∫ H(rankOneEmbedding(g) k) dμ(k)`, where `μ` is the one principal measure
just defined. Their integrals agree. The box, measure and constant depend on the
field, character, rank and principal level, and are independent of `H`.

Only convergence from the original matrix integrand to the averaged scalar
integrand is claimed. Averaging can cancel terms, so this result asserts no
reverse convergence for a general function.

The construction and proof are derived from the UniformBox
calculation, the published box arithmetic, the published left averaging proof,
and Mathlib Haar invariance and Bochner integration. Normalized right averaging
uses the same proof strategy as left averaging, with the right multiplication
shear. No original literature claim, Fourier compatibility or model realization
is used as a premise.
