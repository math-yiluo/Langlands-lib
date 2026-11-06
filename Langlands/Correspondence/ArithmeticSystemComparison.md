# Arithmetic-system and base-reciprocity comparison

`ArithmeticPairEpsilonComparison` relates two supplied common-closure
local-constant systems. It says that the existing
`IsArithmeticPairEpsilonFactor` predicate agrees for both systems, for
every nontrivial additive character, actual pair of parameter classes,
complex unit coefficient and integer exponent. The field and
parameter-carrier universes remain independent. The comparison retains
the existing quantifiers over admissible bottom-field data, continuous
representatives, geometric Frobenius and spectral parameters.

The base-reciprocity helper proves a separate elementary fact:
`IsBaseReciprocity.candidate_unique` identifies two standalone candidates
compatible with one common-closure family. The subgroup fixing the bottom
intermediate field is the entire actual Weil group, by
`IntermediateField.fixingSubgroup_bot`. The two base relations therefore
give equality of the unit values after precomposition with the actual
Weil abelianization projection. Quotient induction and extensionality
identify the original continuous isomorphisms. The second helper first
substitutes an equality of the two common-closure families and then uses
this fact. Neither helper assumes single-field reciprocity uniqueness
or geometric normalization.

The arithmetic comparison for equal families and equal assignments follows
by substitution; proof irrelevance identifies the system certificates.
The final theorem retains two substantive assumptions explicitly:
uniqueness of normalized reciprocity families for this field and
uniqueness of assignments for each fixed family. Each supplied system
contains its family's normalization proof. The first assumption therefore
identifies the two families; the second identifies the two assignments.
Substitution gives the comparison of all arithmetic certificates.

This is an internal API derived from the published actual
`ArithmeticFactors`, `NonabelianSystem` and quotient constructions.
It asserts no new result from external literature. In particular, the
final helper does not prove either of its uniqueness premises. It supplies
neither existence of local-constant systems nor the local Langlands
correspondence. Actual proofs of common-closure reciprocity uniqueness
and of generation sufficient for assignment uniqueness remain separate
prerequisites.
