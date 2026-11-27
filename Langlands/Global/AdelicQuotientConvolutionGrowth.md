# Global growth of compact convolutions on the positive rational quotient

`adelicPositiveRationalConjugateGrowth_allPoints` bounds the positive-rational
subgroup Haar mass of the intersection with `x S x⁻¹` by a fixed power of the
adelic height of `x`, for every adelic `x` and every compact set `S`. The
constant can depend on `S`. `positiveQuotientLpSmoothing_smooth_moderateGrowth`
then gives smoothness and moderate growth for the pointwise convolution of
any `L²` class on the positive rational quotient by an adelic test kernel.

The positive-rational subgroup Haar measure is the product of the normalized
positive-torus measure and counting measure on the rational norm-one
subgroup. The positive factor is unchanged by conjugation. The norm-one
projection commutes with conjugation because the positive image is central.
It follows that the inverse image of the intersection is contained in the
product of a fixed compact positive projection of `S` with the rational
points in the conjugate of its compact norm-one projection. The bound is the
product of the positive mass with the all-point conjugate count
`adelicRationalConjugateCountingAllPoints`.

The quotient convolution estimate `exists_quotientMassBound_representative`
bounds the squared value of a continuous representative of the integrated
right action by the mass of a conjugate of the kernel support times its
inverse support, up to a constant. `positiveQuotientLpSmoothing_ae_eq`
identifies the pointwise convolution with that representative almost
everywhere. They agree everywhere by continuity and positivity of quotient
Haar measure on nonempty opens. The mass bound and the constant comparison
between height and the adelic source norm of `rho` finish the moderate growth
estimate with a uniform exponent.

This follows the counting lemma and convolution estimate of C. Mœglin and
J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
I.2.4–5, pp. 25–27 (PDF pp. 8–10 in
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`). Registered as
`moeglin-waldspurger-1995-spectral-decomposition`, SHA-256
`296dcb3e7170bb0c2689cf0c79136a43cd86976df2b4c51f027cf9365f7fe988`.
The use of the positive-rational Haar product is the adaptation to the split
centre quotient. [Chapter I, Part 2](https://doi.org/10.1017/CBO9780511470905.004)
