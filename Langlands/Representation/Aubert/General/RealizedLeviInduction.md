# Normalized induction through a realized inner parabolic

Author: Worker 1212.

This internal comparison connects actual normalized induction in a represented
dynamic Levi with induction through an ambient simultaneous realization. It
uses the literal subgroup intersections required by induction in stages. It
does not prove induction in stages or a finite-length existence theorem.

## Objects and hypotheses

Let `G` and `L` be affine group schemes over a topological commutative ring `R`.
Let `χ` be a cocharacter of `G` and let a closed inclusion `j : L → G`
represent `Z(χ)`. Both point groups carry the pinned `rationalPointTopology`,
and `Z(χ)(R)` has the ambient subspace topology. The point homeomorphism `e`
is the existing `RepresentedDynamicTransport.pointEquiv`; its ambient value
is postcomposition by `j`.

For a cocharacter `ν` of `L`, suppose an ambient cocharacter `ψ` satisfies
the three exact simultaneous realization identities:

- `P(ψ) = extendFromCentralizer χ j hj P(ν)`;
- `Z(ψ) = Z(ν).map j`;
- `U(ψ) = extendFromCentralizer χ j hj U(ν)`.

These algebraic identities are explicit hypotheses of this comparison.
For connected reductive `G` over any field, the published simultaneous
cocharacter realization theorem supplies such a `ψ`. This module makes no
reductivity claim about `L`.

Separatedness of `G` supplies the extension-intersection identities.
Separatedness of `L` supplies its dynamic semidirect decomposition. The
centralizer membership comparison and its restricted homeomorphism need
neither separatedness hypothesis.

## Actual subgroup and functor comparisons

`parabolic_mem`, `centralizer_mem` and `unipotent_mem` combine the all-test
equalities in `Dynamic.LeviExtensionPoints` with the actual represented
point comparisons. They identify `P(ν)(R)`, `Z(ν)(R)` and `U(ν)(R)` with
the literal `P(ψ)(R).subgroupOf Z(χ)(R)`,
`Z(ψ)(R).subgroupOf Z(χ)(R)` and
`U(ψ)(R).subgroupOf Z(χ)(R)`.

`insideDecomposition` transports the source dynamic semidirect decomposition
along `e`, using these three proved membership equivalences.
`centralizerEquiv` restricts `e` to the compared Levi subgroups.
`unipotentClosed` pulls ambient closedness of `U(ψ)(R)` back first to the
outer Levi and then along `e`, obtaining closedness of `U(ν)(R)`.

For the functor comparisons, both `L(R)` and `Z(χ)(R)` are assumed locally
compact and nonarchimedean. Ambient closedness of `U(ψ)(R)` is also assumed.
The existing represented-point topology results can supply the topology
hypotheses from a closed outer Levi in a locally compact nonarchimedean
ambient group.

`inductionIso` compares induction in the literal inner parabolic followed
by pullback along `e`, with pullback along `centralizerEquiv` followed by
induction in `L(R)`. Both are the existing `normalizedInductionFunctor`
with the Haar half character on the full parabolic. It specializes
`GroupTransport.inductionIso`, whose character transport and projection
comparison establish equality of the actual inducing actions. No
Levi-inflated character or assumed normalization identity replaces that
full-parabolic character.

`inductionIso_hom_eval` states that the component sends an induced function
`f` to the function `y ↦ f(e y)`.
`induction_hasFiniteLength_iff` first transports finite composition length
through the surjective group equivalence `e`, then through the component
isomorphism. The length is over the actual acting group algebra on each
side. No finite-length hypothesis is asserted to hold.

The coefficient carrier universe `uV` is independent of the base and point
universe `u`. Both induction outputs have carrier universe `max u uV`.

## Provenance and boundary

These are derived implementation comparisons. The algebraic inputs are
the literal equalities from `Dynamic.LeviExtensionPoints` and the closed
represented-subgroup point comparisons. The topological and normalized
functor constructions come from `RepresentedDynamicTransport` and
`GroupTransport`. The final length equivalence uses
`FiniteLengthAssembly.finiteLength_comp_surjective_iff` and
`SmoothRep.hasFiniteLength_of_iso`.

This comparison supplies one source-parabolic identification needed for the
exact dynamic induction-of-irreducibles proof. Connected reductivity of the
represented Levi, actual standard-parabolic realization, cuspidal embedding,
supercuspidal induction finite length, and the ambient induction-in-stages
argument remain separate obligations.
