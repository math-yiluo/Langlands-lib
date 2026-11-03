# Restricting actual roots to a central split torus

Author: Worker 1311.

This internal unit constructs the inclusion of the actual rational relative
root span into the kernel of restriction to a supplied central split torus.
It uses the published all-test-scheme definition of centrality and the
independent split-torus adjoint weight decomposition. It assumes no full
root-system realization or character/root complement.

Over any commutative base ring, `IsCentral.adjoint_eq` proves that a central
homomorphism acts trivially on the actual Lie algebra over every test
algebra. Its proof applies all-test centrality to the constant extension of
the given point and the actual dual-number kernel point. The adjoint formula
is conjugation by that constant point, so commutativity cancels the conjugating
factor. `Lie.characterValue_zero` evaluates the zero character as the unit,
and `weightSpace_zero_eq_top_of_isCentral` then identifies the zero weight
space with the full Lie algebra. `weightSpace_le_comp` restricts each
all-test adjoint weight equation along an actual torus homomorphism.

Over an arbitrary field, assume `G` is affine and locally of finite type,
`f : A → T` is a homomorphism of actual commutative group schemes, `A` is a
split torus, and the composite `A → T → G` is central.
`root_restrict_eq_zero_of_isCentral` proves `f ≫ χ = 0` for every actual
relative root `χ` of `T → G`. If the restricted character were nonzero,
the published independent split-torus decomposition would make its weight
space disjoint from the zero weight space. Centrality makes the latter top,
so the restricted weight space is zero. The restriction inequality would
then force the original root weight space to be zero, contradicting the
definition of an actual root.

`relativeRootSpan_le_centralRestrictionKer` and
`relativeRootSpanReal_le_centralRestrictionKer` extend that vanishing to the
rational and real spans of all actual roots. The proofs check each spanning
vector using the existing tensor restriction formula, then apply the universal
property of span. Nonreduced roots and the empty root set are retained.

`relativeRootSpanCentralRestrictionKer` is the resulting rational linear
inclusion into the actual restriction kernel. Its coercion formula states
that it preserves the underlying vector.

The provenance is internal: these are deductions from the existing actual
point, centrality, adjoint-weight and scalar-extension definitions and the
published independent weight decomposition. This unit proves neither a
central embedding into a maximal split torus nor the reverse kernel inclusion,
bijectivity of character restriction from `G`, or the unrestricted complement.

The zero-character evaluation lemma `Lie.characterValue_zero` is reused from
`Lie.TorusCentralizer`.



The weight-restriction theorem `weightSpace_le_comp` is reused from
`Rational.GenericLieWeights`.
