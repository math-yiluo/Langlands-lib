# Bounded sharp-fixer reduction for integer valuations

This internal support module for Task 6309 ports the implemented argument in
`ParahoricFiniteReduction` to `IntegerValuationBuildingData v G` over an arbitrary
field. The valuation is the supplied integer-valued valuation. No local-field
structure or extra apartment axioms are used. `IsBoundedSubset` is precisely
bounded-above image under every real affine functional, matching the boundedness
hypothesis of `UnramifiedZeroFixerAffineRootStatement`.

For one root and a chosen point x₀ of the subset Ω, take an affine functional φ
with that root derivative. Boundedness of -φ gives a bound M. The jump
functionals ψ that are nonnegative at x₀ but negative somewhere in Ω have bounded
value at x₀, since ψ - φ is constant. The published
`IntegerAffineRootLocalFiniteness.finite_bounded_reflectionFunctionals_of_oppositePairs`
(the declaration is in namespace `IntegerValuationBuildingData`) makes these
functionals finite; the published `hasOppositeFactorPairs` supplies its premise.
Choose one negative witness point for each such functional and add x₀. Any root
element fixing that finite subset must fix Ω, by contradiction at its witness.
The reverse inclusion is antitonicity of root fixers. The identity element is
handled separately.

The relative roots are finite by connected reductivity and maximal splitness.
Taking the union of the preceding finite subsets gives one finite subset Ω′
of Ω containing x₀ and preserving every root fixer. Their subgroup supremum
preserves the sharp fixer. The declarations are
`exists_finite_subset_rootFixer_eq_of_mem`,
`exists_finite_subset_rootFixer_eq`, and
`exists_finite_subset_sharpFixer_eq`, all in namespace
`IntegerValuationBuildingData`.

The two comparison theorems then apply the sibling draft
`GenericZeroFixerNormalizerReduction` to Ω′. A pointwise fixer of Ω fixes Ω′;
the finite comparison and sharp-fixer equality give the upper inclusion. The
reverse inclusion follows from pointwise fixation of the constant factor and
sharp-fixer containment. This proves
`subgroup_pointwiseFixer_eq_trivialNormalizer_sup_sharpFixer_of_bounded` and
`subgroup_pointwiseFixer_eq_wholeApartment_sup_sharpFixer_of_bounded` for every
nonempty affinely bounded Ω. Both retain the exact finite normalizer premise
`HasNormalizerSharpFixers`. They assume an arbitrary ambient subgroup containing
every sharp fixer; the first also retains a subgroup of the normalizer acting
trivially on the apartment and mapping into the ambient subgroup.

The provenance is internal: the published finite-reduction proof supporting
KP Lemma 7.7.4 and Proposition 7.7.5(1), with the published explicit-valuation
local-finiteness argument substituted for its local-field instance. The finite
comparison is the implemented generic induction in the sibling draft. This
module does not prove the unconditional normalizer premise, the unramified
sharp-fixer comparison statement, or the final affine-root-sign target.
