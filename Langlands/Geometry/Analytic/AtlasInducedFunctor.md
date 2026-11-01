# Functorial full bounded induction of arbitrary atlas actions

Author: Worker 56. Namespace: `Langlands.Analytic.AtlasInducedAction`.

This internal construction extends `AtlasInducedAction.copiesAction` to a
functor on actual categorical subgroup actions on supplied affinoid atlas
presentations. The complete normed ultrametric field is `K : Type u`, the group
is `G : Type z`, and `H` is any subgroup. All presentations belong to
`AffinoidAtlasPresentation.{u, max z v, max z w} K`, so the coset-copy
objects stay in the same category. No topology on the group, openness,
finite index, nonempty space or nonempty index type is required. Original
charts may overlap or be properly nested.

For every full equivariant arrow `f : X ⟶ Y`, `localMap` is the original
bounded atlas arrow restricted to the same-space nonempty presentations.
`localMap_equivariant` applies functoriality of this restriction to the
original complete equivariance equation. `copiesMap` then uses actual
disjoint-union transport, reindexing cosets by the identity and applying
`localMap f` inside every copy. Its point formula is `(c,x) ↦ (c,f(x))`;
its chosen chart target retains `c` and applies the original target-index
map to the retained original index. `copiesMap_pullback` identifies the
bounded algebra pullback with `f.hom.pullback i.val` exactly, cancelling
the actual identity map of the target inclusion.

`copy_map` proves the restriction equation as equality of entire chosen
arrows. Restricting the two composites to each copy and applying
`localMap_equivariant` at the representative correction proves
`copiesMap_equivariant`. The identity and composition laws likewise use
full-arrow disjoint-union extensionality and the identity and composition
laws of nonempty-chart restriction. These laws compare continuous point
maps, chosen indices and dependent bounded pullbacks; no equality of
algebra maps is inferred from their effect on spectra. They construct
`copiesEquivariantMap` and the actual `copiesFunctor`.

The provenance is internal: the inputs are actual categorical actions and
arrows, and the construction uses the previously constructed nonempty-chart
functor, complete disjoint-union descent, and correction action. It assumes
no output arrow or functor law. Deleting empty charts retains the underlying
space and all original nonempty charts with their genuine algebras and
restrictions, but generally has no inverse in this chosen-chart category.
This module supplies no unrestricted unit from an original presentation.
The normalized unit, arbitrary-target universal extension, quotient transport
of arrows, analytic automorphism continuity, refinement localization and
analytic sites remain separate obligations.
