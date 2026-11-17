# Rational-point translation on actual dynamic coefficient fibers

This internal specialization implements the rational-point translation factors
of Waldspurger V.3 formula (1), printed p.295 / PDF p.61, using the actual
dynamic parabolic, centralizer and contracted radical. It imports the generic
`LeviCoefficientConjugation` construction and the published rational conjugation
interfaces. The source is `waldspurger-2003-plancherel`, DOI
10.1017/S1474748003000082; the original page was read directly.

All declarations are in `Langlands.Plancherel.DynamicCoefficientConjugation`.
The field is any nonarchimedean local field and has its canonical rational-point
topology. The group scheme is affine and locally of finite type; radical
unimodularity follows from the explicit connected-reductivity premise.
The representation carrier has an independent universe.

The three subgroup membership lemmas are obtained from the original functorial
parabolic, centralizer and unipotent conjugation theorems.
`conjugationEquiv_eq` identifies the inverse-image conjugation used by induction
with the inverse of `Langlands.Plancherel.leviConjugation`.
Consequently the target object is exactly the already published
`conjugateRepresentation`, rather than a newly supplied equivalent object.

`leftTranslation` and `dualLeftTranslation` specialize the actual generic maps.
The imported generic laws `CoefficientConjugation.leviLeftTranslation_eval` and
`CoefficientConjugation.leviDualLeftTranslation_eval_apply` describe these maps
before specialization: the function argument is `g⁻¹*x`, and the dual comparison
retains every functional value on the original carrier. This module introduces
no additional evaluation or pure-tensor theorem.
`DynamicOppositeCanonicalScalar.radical_unimodular` discharges both unimodularity
obligations.

`coefficientLeftTranslation` has the literal source-normalized
`leviProductInducedCoefficientObject` fibers. The displayed compact open subgroup
and compact Iwasawa decomposition supply quotient compactness through
`Induction.compactSpace_leftQuotient_of_compact_representatives`.
The ambient rational-point group is second countable by the canonical local-field
instances. Both compactness instances required by the generic product-induction
tensor construction are therefore discharged, rather than assumed separately.
For the target this uses `RationalDynamicSource.conjugateCompact`,
`conjugateCompact_isCompact` and the published
`conjugate_parabolic_mul_compact`. The external `G × G` action law is proved.
Neither compact Haar probability nor any formal degree is rescaled.

These are elementary transport constructions, not standard intertwining
integrals, normalized coefficient extensions, unitarity, integrated coefficient
preservation or the substantive cocycle and descent theorems of V.3.
