# Conjugate subgroup families and evaluation

This is an internal construction derived from the published actual base change,
inner automorphism, subgroup-family evaluation and normalizer APIs. It has an
arbitrary base scheme in universe `u`.

For a group-scheme homomorphism `i : H ⟶ G` and a group-valued parameter
`g : M ⟶ G.X`, `conjugateFamily i g` pulls back `i` to `M` and composes it
with the inner automorphism specified by the actual corresponding base point
of the pulled-back group. No closedness or smoothness is required.

The membership formula projects a point of the pulled-back group back to `G`
and tests its inverse conjugation by the restricted parameter against the
original all-test range of `i`. Evaluating this family along `a : T ⟶ M`
gives exactly the range of the family specified by `a ≫ g`.
`familyTestMap M V` is the structure map from a relative test `V` to `M`,
viewed in `Over S`. `conjugateFamily_conjugator` proves that this structure
map followed by `g` agrees with the projection of the actual pulled-back
conjugator.

The generic lemma `mem_evaluate_iff` applies to any subgroup-family
homomorphism `j`, without a parabolic or monicity hypothesis. It expresses
membership in its evaluation along `a` as membership in the range of `j`
after applying the published `familyPointsEquiv` comparison.

The proof of `evaluate_conjugateFamily` compares the actual
direct and iterated pullbacks, whose projections to the original group agree,
and transports membership through the identity comparison of their relative
tests. It applies the conjugate-family membership formula to both sides.
`range_conjugateFamily_eq_of_normalizer` then proves that parameters `g₁,g₂`
with `g₁⁻¹ * g₂` in the full all-test normalizer of the range of `i` give equal
subgroup functors. Its proof restricts this normalizer element to each
relative test and applies the published conjugation membership equivalence.

This is a generic prerequisite for constructing a universal conjugate family
over a homogeneous quotient. It does not yet descend a family to that quotient
or prove the parabolic-scheme representability target.
