# Uniform Whittaker coefficients from bounded forms on real principal series

`CompactWhittakerCoefficientStatement` starts with a complex-linear form
on the smooth position principal series of a real block list. The form
has a finite bound by compact right-derivative seminorms and transforms
under right translation by the upper unipotent subgroup through the
Whittaker character at `a`. Evaluating the form on right translates and
restricting the source to the K-finite standard module gives
`functionalCoefficient`. This map satisfies all the uniform Whittaker
intertwiner conditions of the Library.

The proof writes the form as a continuous linear functional on a finite
product of spaces of continuous functions on the compact subgroup. The
coordinate map records the compact derivatives used in the bound. The
form vanishes on its kernel. It descends to the range with a norm bound,
then the Hahn–Banach theorem extends it to the whole finite product.

The joint function of two invertible matrices sends `(x,y)` to `f(yx)`.
A matrix right derivative in the second variable acts on the ambient
Fréchet derivative in direction `(0,yX)`. This operation preserves
smoothness on the open product of the unit domains. Induction gives the
joint function for every right derivative word of the translated
vector. Restriction of the evaluation variable to the compact subgroup
gives a smooth family in the supremum norm. Applying the extended
functional proves smoothness of the scalar coefficient.

Differentiation of the translating variable at `x` in direction `xX`
commutes with each derivative in the evaluation variable. Evaluating
the differentiated compact coordinates identifies them with those of
the translate of the derived source vector. Applying the same extended
functional proves the Lie intertwining identity. Multiplicativity of
right translation gives the compact intertwining identity and the
unipotent law. The earlier compact functional growth theorem supplies
the common polynomial exponent for all source vectors.

This proves the construction from bounded forms to uniform coefficient
maps. Applying continuous Whittaker exactness to the given K-finite
maps still requires their realization by such forms on the original
smooth standard module and extension along its principal-series
inclusion.
[Jacquet, *Archimedean Rankin–Selberg Integrals*, Lemmas 2.4 and 3.7 and §11](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
[Casselman, Hecht, and Miličić, *Bruhat filtrations and Whittaker vectors for real groups*, p. 152 and §8](https://www.math.utah.edu/~milicic/Eprints/whittaker.pdf)

## Smooth lower inputs

`CompactWhittakerSmoothRegularityStatement` applies the same smooth coefficient construction to every vector of the smooth position principal series. It proves regularity for all right derivative words and a common polynomial height exponent. The proof builds the derived source vector one direction at a time. The Whittaker law follows from multiplication in the translation action and the covariance of the form. The compact functional growth theorem gives a single exponent for all the resulting source vectors. This is the smooth-input estimate used for the Godement argument of Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §7.2, pp. 47–48.

`exists_commonExponent_compactWhittakerSmoothRegularity` makes the order of choices explicit. One exponent works for all smooth source vectors and all right derivative words. The bounds retain a constant for each vector and word.
