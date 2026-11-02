# Actual adjusted Aubert operator and full Zelevinsky comparison targets

This module is the final specialization of the graded construction to the
actual `Langlands.Aubert.adjustedOperator` from `SupportSign`. It retains
complex coefficients, the current `PadicField` models, independent `uF,uV`
and saturated representation carriers. The additive domain is the actual
exact-K0 direct sum in every natural rank, including zero.

`gradedAdjustedOperator` is the canonical graded additive extension of that
actual support-adjusted operator. Its homogeneous formula is proved, and
its preservation of the actual rank-zero unit follows from the existing
rank-zero identity. No multiplicativity premise is needed for this additive
construction or unit formula.

The exact remaining representation-theoretic targets are
`AdjustedHomogeneousMultiplicativityStatement`,
`AdjustedMultiplicativityStatement`, `AdjustedSegmentExchangeStatement`
and `AdjustedInvolutivityStatement`. They concern the actual adjusted
operator, actual induction multiplication and identified actual segment
classes. The homogeneous-to-whole extension is the published internal
construction in `GradedOperatorComparison`. The segment target is the
unsigned exchange after the support adjustment; the separate unadjusted
identity still has sign `(-1)^(n-k)`.

`AubertZelevinskyComparisonStatement` is equality of integer-linear maps on
the whole actual graded K0 with the additive map underlying the constructed
Zelevinsky endomorphism. `adjustedRingEndomorphism` constructs the actual
ring endomorphism once its multiplicativity target is proved; unit
preservation is already supplied. `AubertZelevinskyRingComparisonStatement`
is equality of ring endomorphisms.
`AubertZelevinskyInvolutionComparisonStatement` compares the whole additive
operator with the constructed Zelevinsky ring involution when that
involutivity proof is supplied.

`AubertTheorem23Statement` retains the full whole-ring scope: actual
adjusted multiplicativity, involutivity of the constructed Zelevinsky
endomorphism and equality of the two additive operators on every class.
Its parameters explicitly name binary exactness, induction ring laws and
the actual polynomial comparison. These are lower proof obligations,
not automatically permitted external Chapter V structure.

The sources are Aubert 1995, Definition2.1, Remark2.2 and Theorem2.3,
printed pp.2184–2185, with the corrected product-Levi tensor paragraph and
Theorem1.7(2) citation, and Zelevinsky1980, Corollary7.5 and §9.12.
The passage from generators to all classes requires the actual polynomial
comparison, equivalently the monomial basis result, together with
multiplicativity and unit preservation. An additive map calculation on
individual segment generators alone does not prove this theorem.

All existing GL classification and representation-theoretic dependencies
of `SupportSign`, the exact graded product and the actual segment choices
remain present. The body/type dependency inventory accompanying the final
source map records their transitive helper declarations. No new structural
model or generality beyond these actual GL local-field models is asserted.
