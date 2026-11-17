# Generic equivalence and actual translated tensor factors

This internal algebraic continuation of `ActualConjugateLeviTensor` uses
Waldspurger (2003), V.3 formula (1), printed p.295 / PDF p.61, registered as
`waldspurger-2003-plancherel`. It supplies the equivalence underlying that
constructed generic comparison and a pure-tensor formula for its actual
translation component. All hypotheses and actual objects are retained:
an arbitrary nonarchimedean local field, affine locally finite type
connected reductive ambient group, independent representation carrier
universe, the full actual parameter algebra, displayed compact Iwasawa
representatives and the two specified actual continuation packages.

`translatedCoefficient_tmul` states the pure-tensor formula in expanded
form: actual coefficient left translation is followed by pointwise
positive-Levi inducing transport for the canonical conjugate-twist
equivalence. After the existing product-induction comparisons this sends
the two factors through actual vector left translation and actual smooth-dual
left translation, followed respectively by that inducing equivalence and
its inverse smooth-dual pullback. Its left side is the expression defining
`translatedCoefficient`, with the existing actual components expanded;
its right side keeps the same coordinate order.

The proof first establishes this composition law for arbitrary displayed
semidirect decompositions, actual subgroup conjugation comparisons and
an inducing equivalence. It uses the published pure-tensor translation
law and the preceding `coefficientCongr_tmul`. It then specializes to the
actual dynamic parabolics and to `conjugateTwistEquiv`; no free comparison
map or compatibility square remains as a premise. The expanded theorem
statement retains the actual inducing source object of the generic
translation construction, avoiding expensive conversion between two
presentations of the canonical conjugate representation.

`genericComparisonEquiv` packages the already constructed rational-point
comparison as a representation equivalence on its genuine simultaneous
regular and bijective locus. It is `translatedCoefficient` followed by
the equivalence attached to the particular actual common-Levi comparison
using its proved generic bijectivity. Its underlying function is thus the
two-factor composite defining `ActualConjugateLeviTensor.genericComparison`.
This does not choose an unrelated equivalence or replace any standard
operator. The domain is the same pulled-back actual generic locus, and
the target uses the actual restricted conjugate parameter.

`genericComparison_bijective` proves bijectivity for that exact composite
function, written as common-Levi comparison composed with actual
translated coefficient transport. The proof composes the published
common-Levi generic bijectivity theorem with the constructed translation
equivalence's bijectivity. The construction and theorem introduce no
analytic existence, nonempty/dense generic-locus or all-unitary claim.

The actual coefficient fibers, positive Levi normalization, actual
contragredient, compact Haar probability coefficient maps and source
formal degrees remain the existing ones. This unit proves neither an
integrated coefficient identity nor an all-unitary extension, form
identity, cocycle or descent law. A dedicated single assembled
forward/inverse-reverse pure-tensor equality and its evaluation lemma
remain further work; the translation formula here and the imported
common-Levi formula prove the separate algebraic stages.
