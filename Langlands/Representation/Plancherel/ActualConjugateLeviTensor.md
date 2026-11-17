# Actual translated common-Levi coefficient tensor

This internal construction implements the rational-point translation
component of Waldspurger (2003), V.3 formula (1), printed p.295 / PDF p.61,
registered as `waldspurger-2003-plancherel`. It composes actual coefficient
translation with the actual common-Levi forward/inverse-reverse-dual tensor.
It uses the existing positive-Levi product-induced coefficient objects;
no coefficient-preserving comparison is supplied as an input.

The field is any nonarchimedean local field. The ambient group scheme is
affine, locally of finite type and connected reductive. The field and the
representation carrier have independent universes. There is no splitness,
characteristic-zero, positive-rank or irreducibility-of-induction premise.
This algebraic construction works for an arbitrary smooth inducing object;
the later discrete-series and unitary-extension targets are separate.

The source parabolic is the actual dynamic parabolic of `χ`. Rational
conjugation by `g` gives the cocharacter `χg = χ ≫ (G.innerIso g).hom`.
The target cocharacter `ψ'` is supplied with equality of its centralizer
subgroup functor to that of `χg`. Compact open representatives are displayed
for the source, and separately for both `χg` and `ψ'`; their Iwasawa
factorizations discharge the compact-quotient obligations. All rational-point
topologies and every rational-character norm are the canonical actual ones.

`coefficientCongr` lifts an inducing equivalence pointwise through the
actual positive-Levi induction from the product parabolic. Its product-Levi
map is the existing `productCoefficientLeviEquiv`: vector transport tensored
with inverse pullback on the actual smooth dual. `coefficientCongr_eval`
proves its evaluation formula. `coefficientCongr_tmul` proves its two-factor
formula through the actual product-induction tensor equivalence. The proof
compares evaluations at every pair of group elements, using the published
tensor evaluation law. No integration or change of duality scale occurs.

`translatedVector` and `translatedDual` use the published actual dynamic
left translations. On induced functions their translation component is
`f(x) ↦ f(g⁻¹*x)`, and the dual component retains the actual same-functional
conjugation identification. They then lift the canonical
`ActualConjugateLeviTwist.conjugateTwistEquiv` and its inverse smooth-dual
pullback. Their target inducing object is exactly the full transported
twist of `conjugateRepresentation χ g A`.

`translatedCoefficient` performs these two operations on the actual
product-induced coefficient space: `coefficientLeftTranslation`, followed
by `coefficientCongr` for that same canonical conjugate-twist equivalence.
It is an actual representation equivalence from the coefficient fiber for
`A` twisted by `z` at `χ`, to the fiber for the conjugate base object twisted
by `conjugateParameter χ g z` at `χg`. The equivalence is constructed, not
chosen as an arbitrary identification of coefficient spaces.

The forward and reverse continuation inputs are the published
`ActualCommonLeviTensor.ContinuedPair` packages for `χg` and `ψ'`, on the
canonical conjugate object and its actual smooth contragredient. They retain
their squared-modulus compatibility, nonempty open starting regions, source
quotient measures and whole-operator continuation denominators. The reverse
dual operator is evaluated at the inverse parameter through the published
functional-preserving dual-twist comparisons. No continuation-existence,
generic-bijectivity or induced-irreducibility theorem is inferred.

`genericLocus` is the inverse image, under full parameter conjugation, of
the actual common-Levi simultaneous regular and bijective locus of those
two particular operators. `genericParameter` restricts conjugation to this
locus. The set is not asserted to be nonempty or dense. It is a construction
domain; it does not replace the full unitary domain of a closed extension
target.

`genericComparison` is the composite of `translatedCoefficient` with
`ActualCommonLeviTensor.genericComparison` at `genericParameter`. Thus the
standard-operator component is the actual forward continued operator
tensored with the inverse of the particular reverse induced-dual operator.
Its endpoints are the literal source-normalized coefficient fiber at
`(χ,A,z)` and the target fiber at
`(ψ',conjugateRepresentation χ g A,conjugateParameter χ g z)`.
`genericComparison_action` proves its elementary intertwining law for
every coefficient vector and every pair of actual rational points, by the
constructed intertwining map's own action equality.

The translation, inducing-transport and common-Levi components have their
published or above-proved pure-tensor and evaluation laws. This focused unit
stages their constructed composite and its action law; dedicated assembled
pure-tensor, evaluation and generic-bijectivity lemmas remain subsequent
work. It supplies no unitary extension, coefficient identity, form identity,
cocycle or Weyl descent theorem. The compact Haar probability coefficient
map and the source formal degree are untouched; the construction introduces
no new measure, scalar or quotient-duality normalization.
