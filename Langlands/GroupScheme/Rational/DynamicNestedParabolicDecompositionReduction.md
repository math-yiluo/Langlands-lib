# Standard-index comparison for nested dynamic decompositions

This module is an internal conditional bridge. It proves no unconditional
reductive-group structural assertion. Its inputs are the proposition
targets `DynamicNestedParabolicDecompositionStatement`,
`StandardCocharacterStatement` and `StandardParabolicOrderStatement`.

`nestedLeviDecomposition_standard_of_dynamic` fixes an arbitrary field,
a connected reductive `G`, an ambient maximal split torus `i : T → G`,
a generic cocharacter `ν`, and `J ⊆ K ⊆ simpleRelativeRoots i ν`.
It concludes
`SubgroupFunctor.NestedLeviDecomposition P_J M_J N_J M_K N_K`
for the actual published `standardParabolic`, `standardLevi` and
`standardUnipotent` functors. Consequently all three products of the
dynamic conclusion hold on every test scheme, as does the normal
complement decomposition of `M_K ∩ P_J`.

The implemented proof chooses standard cocharacters `α` for `J` and
`β` for `K` from `StandardCocharacterStatement`, including the three
equalities of standard and dynamic functors for each cocharacter.
`StandardParabolicOrderStatement` gives `P_J ≤ P_K` and `M_J ≤ M_K`.
Transporting these two inclusions through the realizing equalities
constructs `Dynamic.IsCompatibleNestedPair` in the original maximal
split torus. The dynamic target gives the conclusion, and rewriting
the realizing equalities returns the standard functors. The bridge
does not use the order target's unipotent inclusion.

`standardLeviIntersectionStatement_of_dynamicNestedParabolicDecomposition`
extracts the first four all-test conjuncts of this result and evaluates
the second set product at the identity test. These are exactly the
all-test complement and rational-point product in the existing
`StandardLeviIntersectionStatement`. No statement or Markdown of that
existing target is changed. Its proof task
`1d7d4767-a668-4ce1-9989-319a625f6de3` is retained.

This is a formal relation between the interfaces for the nested
decompositions in Renard V.3.10–V.3.11 (printed p.112, PDF p.118)
and VI.1.4 (printed p.136, PDF p.142). Its provenance is the internal
specialization and the published standard-cocharacter/order interfaces;
it is not an independent proof of those source results. The arbitrary
field and nonreduced-test scope is inherited from those interfaces and
the dynamic proposition.
