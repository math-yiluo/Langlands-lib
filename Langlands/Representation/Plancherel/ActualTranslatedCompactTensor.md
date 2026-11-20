# The compact composite of actual translation and the standard tensor

This construction reads Waldspurger’s formula V.3(1) in the fixed
compact pictures of IV.1. The source is Waldspurger (2003), printed
pp. 276–277 and 295, PDF pp. 42–43 and 61, registered as
`waldspurger-2003-plancherel`.

The base field is an arbitrary nonarchimedean local field. The affine,
locally finite type ambient group is connected reductive, and the
representation-carrier universe is independent of the field universe.
The displayed compact open subgroups and Iwasawa factorizations give the
published source and conjugate compact tensor charts. The full parameter
is the unramified character of the represented source Levi.

`compactTranslation` transports the actual ambient
`ActualConjugateLeviTensor.translatedCoefficient` through those charts.
This ambient map applies left translation to the two induced factors and
then the canonical conjugate-twist comparison. The dual factor uses the
inverse pullback on smooth functionals. The charts retain the existing
positive Levi normalization and the actual compact carriers.

`compactComparison` composes this map with `pulledBackStandardTensor`.
The latter applies the particular forward standard continuation and the
inverse of the particular reverse-dual continuation after conjugation of
the full parameter. Its domain is exactly the preimage of the simultaneous
regular and invertible locus of the two continuations. The proposition
`AgreesWithV3CompactChart` records the remaining Lean identification with
the compact chart of the ambient generic map used in the closed V.3.1
germ.

`compactComparison_clears` proves that if the actual compact translation
is polynomial, every regular scalar clearing the pulled-back standard
operator also clears the composite. The proof uses polynomial operator
composition, moving the scalar through a composition of linear maps.
`compactComparison_rational_of_polynomialTranslation` uses the explicit
`ScalarInverseData` of the standard tensor to choose one denominator for
all inputs. Polynomiality of the compact translation is an explicit
premise of these two lemmas. Analytic continuation existence, scalar
composition and regular extension across the whole unitary orbit are
separate obligations.
