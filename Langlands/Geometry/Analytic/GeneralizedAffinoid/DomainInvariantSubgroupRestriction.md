# Restricting invariant represented-domain diagrams to smaller open subgroups

Author: Worker 56.

## Setting and construction

Fix a complete ultrametric normed field `K : Type u`, an actual finite
positive-polyradius affinoid quotient `P : PresentedAffinoidAlgebra K`,
a topological group `G : Type v`, and a represented-domain spectral action
`ρ : DomainSpectralAction G P`. The two universes remain independent.
The declarations introduced here are in the namespace
`PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction`.

For open subgroups `J ≤ H` of `G`, the module reuses
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.openSubgroupInclusion`
from `StrictTestDomain.InvariantSubgroupRestriction`. This continuous group
homomorphism `J → H` sends each element to the same element of `G`, carrying
the supplied proof of subgroup inclusion. Continuity follows from the
induced subgroup topologies.

`invariantDomainRestriction ρ h` sends an `H`-invariant represented domain
to the same representation regarded as `J`-invariant. Its new invariance
proof is the composite inequality `J ≤ H ≤ locusOpenSubgroup ρ d`.
It retains every actual bounded restriction between domain
representations. It is the full-subcategory inclusion supplied by
Mathlib's `ObjectProperty.ιOfLE`, and is full and faithful.

The object and arrow lemmas expose these unchanged data.
`invariantDomainRestriction_forget` identifies its composite with the
full inclusion into `Domain K P`. The reflexive restriction is the identity
functor, and restrictions compose along nested subgroup inclusions.
These equalities are definitional, using proof irrelevance for the
invariance witnesses.

## Actual bounded actions and spectrum diagrams

`invariantSectionAction_subgroup` identifies the bounded section-action
homomorphism on the reinterpreted domain with the original action
precomposed by `J → H`. This is equality of homomorphisms into
`Aut d.obj.algebra`, including the full bounded maps and their inverses.
The section action was constructed from the domain's full representing
property; the comparison does not use separation of algebra elements
by spectrum points.

`invariantAffinoidActionFunctor_subgroup` identifies the entire affinoid
action diagram after restriction of domains with the original diagram
followed by Mathlib's `Action.res` along `J → H`. The geometric objects
remain the opposites of the actual section algebras. The group operators
remain the opposites of the inverse bounded section maps, and the
arrows remain the opposites of the actual bounded restrictions.

`invariantSpectrumActionFunctor_subgroup` gives the corresponding equality
of functors into `Action TopCat J`. In particular it preserves the
formulas

```text
(g • x)(b) = x(sectionAction(g).inv(b)),
restrictionComap(f)(x)(b) = x(f.restriction(b)).
```

## Structural maps over the original spectrum

`restrictedGlobalSpectrumAction_subgroup` identifies the global action
restricted first to `H` and then to `J` with its direct restriction to `J`.
`invariantSpectrumActionToBase_subgroup` identifies the equivariant
structural map of each reinterpreted domain with the original map
restricted along `J → H`. Its underlying map is still the continuous
pullback along `d.obj.baseMap`.

Finally, `invariantSpectrumActionOverFunctor_subgroup` compares the
entire diagrams in the overcategory of the restricted original spectrum
action. The right-hand side applies `Over.post` to the subgroup-restriction
functor. This retains the original structural maps, every actual spectrum
restriction and its commuting triangle. All the action and overcategory
comparisons are definitional equalities.

## Provenance and scope

This is an internal consequence of the previously constructed full
represented-domain category, its bounded section actions and its
equivariant spectrum-over-base diagram. The construction uses the
published Mathlib full-subcategory inclusion, action restriction and
overcategory functor. No new literature theorem is asserted.

Empty domains, empty spectra, zero quotients, nilpotents and trivial scalar
valuations are allowed. The action target has continuous operators for
each fixed group element. Joint continuity remains a separate analysis
obligation. These comparisons construct restriction compatibility for
the supplied represented-domain diagrams; general analytic spaces,
structure sheaves, analytic etale sites and the Harris specialization
remain further work.
