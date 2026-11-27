# Positive-rational subgroup mass in conjugates of compact sets

`adelicPositiveRationalConjugateGrowth` bounds the canonical subgroup Haar
mass in `AdelicPositiveRationalConjugateGrowthStatement`. Let `G` be affine
and locally of finite type over a number field, with a closed matrix
embedding of positive size. The central morphism `i` comes from a torus
presented as a finite product of copies of `Gₘ`, and restriction of rational
characters along `i` is injective with finite-index image. For the canonical
`positiveRationalSubgroupHaarMeasure`, one height exponent works for all
compact sets being conjugated and for all compact sets of finite adelic
components of the conjugating element. The constant can depend on the two
compact sets.

The positive-rational subgroup measure is the product of positive-torus
Haar measure and principal counting measure. Conjugation leaves the
positive projection unchanged because the positive factor is central. The
norm-one projection of a conjugate is the conjugate of the norm-one
projection. The preimage of the subgroup intersection is therefore
contained in the product of a fixed compact set in the positive factor
and a finite set of principal points. The theorem
`Langlands.Global.adelicRationalConjugateCounting` bounds the second factor
by the stated height power. The finite mass
of the first factor gives the constant in the estimate.

This is a bound for the subgroup mass entering pointwise convolution on
the positive rational quotient. It supplies the polynomial estimate used
before the uniform cuspidal convolution estimate of Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), Lemma 9.3.3,
pp. 247–248.
