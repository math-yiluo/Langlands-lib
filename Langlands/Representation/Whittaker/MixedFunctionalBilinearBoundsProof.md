# Separate-group functional-factor and finite-exception assembly

This module proves the published closed proposition
`Langlands.MixedBilinear.FunctionalFactorAssemblyStatement.{uG, uH, uI, uS, uZ, uV, uW}`
from `Langlands.Representation.Whittaker.MixedFunctionalBilinearBoundsStatement`.
The proof is internal algebra on published constructions. It extends the
same-group assembly patterns in `Whittaker.FunctionalBilinearBounds` and
`Whittaker.FiniteLengthBilinearBounds` to the actual mixed covariance spaces of
`Filtration.MixedBilinear` and uses the published mixed-filtration bounds in
`Filtration.MixedBilinearBoundsProof`. No original-literature claim is added.
The statement pair and its imports are preserved.

The two representations belong to independent groups `G` and `H`. Their
carriers, the groups, the test type `I`, the parameter type `S`, and the spectral
type `Z` occupy seven independent universes. Every conclusion uses the actual
extended-natural module length `MixedBilinear.length a b χ ρ σ`, with its
published argument order. The test maps `a : I → G` and `b : I → H` are
arbitrary functions; the proof never chooses a test, so `I` can be empty.

## Implemented components

`MixedBilinear.length_le_one_of_unique_functional_factors` takes actual
filtrations `f : ObjectRepFiltration A m` and `g : ObjectRepFiltration B n`,
one unique functional position in each, detection of both functionals by
nonzero graded-pair length, and the conditional length bound for functional
pairs. Let the unique positions be `i₀` and `j₀`. If a different pair had
nonzero length, detection and uniqueness would force its indices to be `i₀`
and `j₀`, a contradiction. Thus all other lengths vanish.
`MixedBilinear.length_le_of_single_pair` bounds the total length by the
selected pair's length, and its conditional bound gives at most one.

`MixedBilinear.exists_exception_length_le_one_of_unique_functional_factors`
chooses the finite exceptional set for every actual pair of graded positions
and uses `InvariantBilinear.gradedExceptionSet` to take their finite union.
The avoidance lemma
`InvariantBilinear.not_mem_pair_of_not_mem_gradedExceptionSet` supplies both
pair-control implications for every pair outside this union. The preceding
length theorem then applies for each parameter. The union is chosen before
the parameter `s`, hence before every form. Every exceptional set contains
spectral values `z s`; no algebraicity or other regularity of `z` or `χ` is
used.

`MixedBilinear.exists_exception_length_le_one_of_functional_equiv` applies
`Whittaker.existsUnique_hasFunctional_factor` twice: once over `G` and once
over `H`. Its hypotheses are smoothness of both total representations,
compact-limit containment for the respective character subgroups, local
constancy of the two scalar characters, and linear equivalences of the two
total functional spaces with `ℂ`. It passes the resulting unique positions
to the finite-union theorem. These supplied filtrations need neither simple
nor nonzero quotients.

`ObjectRepFiltration.isAdmissible_gradedRepresentation` proves the transfer
used in the fourth component. For a filtration `g` of an admissible
representation `B` of a topological group `H`, it constructs the actual
intertwiner from the upper step `g.subrepresentation j.succ` into `B`.
`Langlands.isAdmissible_of_injective` transfers admissibility along this
injective inclusion. Then
`Unramified.SphericalExistence.isAdmissible_of_surjective` transfers it along
`(g.gradedProjection j).hom`, using `g.gradedProjection_surjective j`.
The latter transfer uses exactly the assumption that every open subgroup
of `H` contains a compact open subgroup.

`MixedBilinear.exists_exception_length_le_one_of_admissibleSecond_finiteLength`
chooses actual simple filtrations for both representations with
`ObjectRepFiltration.ofFiniteLength`, using the supplied finite lengths over
their respective group algebras. The first graded factors are smooth by
`ObjectRepFiltration.isSmooth_gradedRepresentation`. The second graded factors
are admissible by the preceding transfer lemma. Simplicity of the chosen
factors gives their irreducibility, so the supplied irreducible-pair premise
provides the required exceptional sets. The functional-equivalence component
then applies, using smoothness of the second total representation from its
admissibility.

This last component keeps admissibility of the second total representation
and requires admissibility of the second factor in the pair premise.
Compact-open cofinality is assumed only for `H`; no such condition is used
for `G`. The first representation needs only smoothness. Admissibility is
never inferred from smooth irreducibility.

## Exact targets and scope

The four closed theorems
`uniqueFunctionalFactorsLengthBound`,
`uniqueFunctionalFactorsFiniteException`,
`functionalEquivFiniteException`, and
`admissibleSecondFiniteLengthException` prove their respective published
Prop-valued statements. Each introduces all quantified data and applies its
reusable component lemma. The closed theorem `functionalFactorAssembly`
packages them in the exact published conjunction order, with no outer term
parameters and all seven independent universes.

All finite unions and filtration bounds retain actual positions, including
repetitions and zero quotients wherever the premises permit them. Infinite
lengths are interpreted in `ℕ∞`. Pair control remains an explicit hypothesis
throughout: this proof supplies neither source rigidity nor a compact/generic
pairing, mirabolic restriction finite length, or full unequal-rank uniqueness.
