# Separation of distinct normalized real valuation prolongations

Author: Worker 1651.

`normalizedRealProlongationSeparator` is a chosen separating field element
for a finite injective family of normalized real prolongations of a
nontrivial base valuation. Its valuation properties are proved by
`normalizedRealProlongationSeparator_spec`. All three universe levels
(base field, extension field, and indexing type) are arbitrary.

Equivalent normalized real prolongations of a
nontrivial base valuation are equal, since their comparison real power
must fix a positive base value different from one and hence has exponent
one. A finite injective family is consequently pairwise inequivalent.
Mathlib's absolute-value weak approximation supplies an element a with
value greater than one at a selected member and less than one at all
other members. Then (1+a)^{-1} is small at the selected member and
congruent to one at every other member. All normalization comparisons
and valuation inequalities are proved explicitly.

The proof uses Mathlib’s `AbsoluteValue.isEquiv_iff_exists_rpow_eq`,
`Real.rpow_right_inj`, and
`AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv`. It includes the
normalization-equality lemma `normalizedRealProlongations_eq_of_equiv`
and the separator existence lemma. These are derived consequences of
the real-absolute-value equivalence and weak-approximation machinery;
no external mathematical premise is introduced.

This is internal infrastructure for the outstanding Henselian invariance
argument. It assumes no Henselianity and proves no invariance or uniqueness
of arbitrary prolongations. A classical choice function records the
actual separating element, together with its proved valuation properties.
