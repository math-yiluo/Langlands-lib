# Actual parabolic comparison from contracting subgroups

This derived module proves an all-test parabolic comparison and constructs the
actual inclusion-compatible isomorphism of its affine representatives.

For a separated group scheme over any base, the generic theorem
`Dynamic.parabolic_le_of_unipotent_centralizer_le` proves that inclusion of both
the contracting and centralizer subgroup functors implies inclusion of the
parabolic functors. For a parabolic point p, take its actual orbit limit l.
The published limit theorems put p*l^-1 in the contracting subgroup and l in the
centralizer. Their images therefore lie in the target parabolic, and their
product is p. Two inclusions give
`Dynamic.parabolic_eq_of_unipotent_centralizer_eq`. These statements hold on
every scheme test and require no reductivity or affineness.

The split specialization assumes a reductive affine group over a nontrivial
commutative ring, one actual split fibrewise maximal torus, a supplied full
fibrewise coordinate root datum and actual root parametrizations. Two coordinate
cocharacters are assumed to have equal actual contracting subgroup functors.
The published actual root-sign detection fixes the same positive and zero-root
sets. `SplitCentralizerComparison` consequently gives equality of their actual
centralizers. The generic limit decomposition then proves equality of the actual
parabolics in `AffineRegularBorel.parabolic_eq_of_unipotent_eq`.

`parabolicIsoOfUnipotentEq` is the resulting actual group-scheme isomorphism
between the two specified affine dynamic parabolic representatives, with the
exact ambient inclusion equation proved by its companion theorem. The names
`borel` and `inclusion` come from the existing `AffineRegularBorel` interfaces;
this comparison places no regularity or strict root-positivity hypothesis on
the two cocharacters.

Equality of parabolics and their representative isomorphism are conclusions.
The torus is fixed, and the nontrivial-ring assumption in the specialization is
explicit. Identifying the original contracting group with a canonical face
cocharacter, different-torus filtration compatibility, and effective descent
remain separate steps of the finite vector-bundle filtrations of supplied
relative radicals.
