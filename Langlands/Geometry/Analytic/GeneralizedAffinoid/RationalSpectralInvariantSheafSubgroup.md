# Subgroup coherence for the actual invariant rational algebra sheaf action

Let `K : Type u` be a complete ultrametric normed field, `A` an actual
positive-polyradius presented affinoid algebra, and `ρ : DomainSpectralAction G A`
a represented-domain spectral action of a topological group `G : Type v`.
Let `H ≤ J` be open subgroups. Field, group and general coefficient universes
remain independent.

A `J`-invariant rational chart is also `H`-invariant, with the same quotient
algebra and bounded restriction arrows. The published continuous functor
`spectralInvariantChartRestriction ρ h` includes those charts into the
`H`-invariant category. Its sheaf functor therefore runs from sheaves on the
`H`-invariant site to sheaves on the `J`-invariant site, by exact presheaf
precomposition. The acting-group restriction runs from `J` actions to `H`
actions. These directions agree in the comparison constructed here.

## Sheaf and action coherence

`spectralInvariantSheafRestriction_refl` and
`spectralInvariantSheafRestriction_comp` are equalities of entire sheaf
functors for arbitrary categorical coefficients, not merely of section
values. They follow by unfolding the actual precomposition functors.
Nested changes `H ≤ I ≤ J` retain the very same original charts and maps.

`spectralInvariantSheafAction_subgroup` identifies the two complete actions
by definitional equality, including their underlying ordinary sheaves and all
their original section operators.

`spectralInvariantSheafActionSubgroupIso ρ h` compares two actual actions of
`H` on ordinary sheaves on the finite `J`-invariant rational site. On its
source, restrict the sheaf carrying the constructed `H` action along the
chart inclusion. On its target, restrict the acting group of the constructed
`J` action to `H`. The complete underlying presheaves agree. The comparison
lifts their identity natural isomorphism to sheaves and then to actions.
Every original bounded section operator agrees on the two sides, which proves
its equivariance. Both its forward and inverse components are the identity
algebra homomorphism on each original chart algebra, as the two application
equations state. No additional sheafness or action output is assumed.

`spectralInvariantSheafActionSubgroupIso_eqToIso` identifies this particular
comparison with the isomorphism induced by the equality of the complete
actions. `spectralInvariantSheafActionSubgroupIso_refl` states that changing
`H` to itself gives the identity isomorphism of the entire sheaf action.

For `H ≤ I ≤ J`, `spectralInvariantSheafActionSubgroupIso_comp` identifies
the composite of two mapped comparison isomorphisms with the direct `H ≤ J`
comparison. First, the sheaf restriction from the `I`-invariant site to the
`J`-invariant site maps the `H ≤ I` comparison, using `Functor.mapAction H`.
Then, acting-group restriction from `I` to `H` maps the `I ≤ J` comparison,
using `Action.res`. The intermediate actions, both possible source actions,
and both possible target actions agree definitionally: sheaf precomposition
composes exactly and the subgroup inclusions retain the same group elements.
Thus the equation is an equality of the full isomorphisms of actions in the
same category, including their inverses. The proof reduces equality of
isomorphisms to equality of forward morphisms, then uses extensionality for
action morphisms, sheaf morphisms and natural transformations. The original
component algebra maps are identities, so the final equalities are reflexive.

## Original section and structural maps

`spectralInvariantSheafSectionAction_subgroup` identifies the complete
evaluated section actions with acting-group restriction of those for `J`.
`spectralInvariantBaseAlgebraAction_subgroup` does the same for the ambient
algebra action. `spectralInvariantSheafSectionRestriction_subgroup` retains
each entire equivariant algebra restriction along an original chart arrow.
These are definitional equalities, retaining every operator at the original
group element and every original restriction.

`spectralInvariantWholeSectionIso_subgroup` identifies the entire particular
isomorphism of actions from the ambient algebra to whole-chart sections with
the acting-group restriction of the one for `J`. Both its forward original
whole-chart structural map and its inverse whole retraction are retained.
The whole chart itself is unchanged under subgroup change.
`spectralInvariantSheafBaseMap_subgroup` identifies the entire equivariant
structural algebra homomorphism on every chart, including its source and
target actions. These two equalities also follow by unfolding the original
constructed maps; they do not choose unrelated comparison isomorphisms.

## Provenance and scope

This is an internal coherence construction from
`RationalSpectralInvariantSheafAction`, the continuous subgroup chart and
sheaf functors in `RationalSpectralInvariantRestrictionSite`, the unchanged
bounded action restriction in `RationalSpectralInvariantRestriction`, and
Mathlib's `Action.res`, `Functor.mapAction`, `Action.mkIso` and
`ObjectProperty.isoMk`. It asserts no new original-literature result.

The scope is algebraic actions on the proved ordinary algebra sheaf on the
finite invariant rational sites of one actual affinoid. Arbitrary positive
radii, supported trivial valuations, nilpotents, zero algebras, empty spectra
and empty finite covers are retained. No norm or discrete continuity of
algebra sections is asserted. Full invariant-domain or analytic etale sites,
unrestricted atlas gluing and the Harris tower remain separate obligations.
