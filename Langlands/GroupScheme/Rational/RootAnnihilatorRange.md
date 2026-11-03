# Integral criteria for real annihilator range comparisons

Author: Worker 1322.

This derived unit supplies algebraic criteria for exact range comparisons in the
existing real cocharacter spaces of actual commutative group schemes.

`IntegralRootAnnihilatorSpanStatement` states the integral-span assertion
uniformly over arbitrary fields, actual commutative group schemes and finite
character selections, at arbitrary universe. The final theorem
`integralRootAnnihilatorSpanStatement` proves this proposition using the span
lemma below. The other lemmas give its range-comparison consequences.

For a finite character selection `J`, `rootAnnihilator_eq_span_integral` expresses
the published real annihilator as the real span of `1 ⊗ ν`, for actual integral
cocharacters `ν` annihilated by every character in `J`. The proof applies the
published integral-annihilator base-change equality and Mathlib's description
of scalar extension as a span. Thus `rootAnnihilator_le_iff_integral` checks
containment in any real submodule using precisely those integral cocharacters.

For an actual morphism `f : A → T`,
`range_cocharacterMapReal_le_rootAnnihilator_iff` identifies containment of the
entire real cocharacter image in the annihilator with vanishing of all integer
pairings on the integral cocharacter image. This equivalence does not require
finiteness of `J`. The forward implication evaluates at pure tensors `1 ⊗ μ`
and uses injectivity of the integer-to-real map. The reverse implication uses
tensor induction and the pure-tensor evaluation formula.

With finite `J`, `rootAnnihilator_le_range_cocharacterMapReal` proves the reverse
real containment from integral annihilator containment in the integral
cocharacter image. It applies the span criterion, mapping each integral
factorization to its pure tensor. Finally,
`range_cocharacterMapReal_eq_rootAnnihilator` combines the two containments when
the integral image equals the integral annihilator.

The provenance is internal linear algebra from the existing character pairing
and the integral-annihilator base-change result. No external source is used.
These statements assume the displayed integral factorization or vanishing
conditions; they do not prove them for standard Levi subgroups or split
components, and do not prove the unrestricted standard-Levi target.
