# Actual bounded local-domain restrictions under subatlas selection

Author: Worker 36.

This module constructs the functor from actual local domains of a locally
refining selected subatlas to those of the original atlas. It preserves the
entire presented affinoid algebra, its ambient map and every bounded
restriction. The functor is fully faithful, and identity algebra
isomorphisms give a natural isomorphism of its presented-affinoid diagram.

## Source and provenance

This is derived infrastructure for Berkovich, *Etale cohomology for
non-Archimedean analytic spaces*, Publications mathematiques de l'IHES 78
(1993), Proposition 1.2.13(i)-(ii), printed p.21 / PDF p.18. The registered
original is `berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Part (i) compares completed domain families under equivalent nets. Part (ii)
constructs canonical bounded restrictions for contained domains in the
extended atlas.

The particular functor and full restriction identities below are internal
consequences of the already implemented full affinoid-domain universal
properties and finite-cover separation. The original does not formulate
this chosen-presentation functor or its diagram isomorphism. This unit
supplies those comparisons for a locally refining selection of original
charts; it does not assert the whole equivalent-net conclusion of (i).

## Inputs

The field `K` is a complete ultrametric normed field, and `X` is a topological
space. The actual `IndexedAffinoidAtlas K X` is denoted by `a`. The predicate
`P` selects original chart indices, and `hP : a.IsLocallyRefiningSelection P`
ensures that their family is again an atlas on `X`. The field, ambient space
and chart indices have independent universes `u`, `v` and `w`.

The input atlas retains its presented quotient algebras, embedded spectra,
net, actual full-domain restrictions and their compatibility. No additional
global Hausdorffness, reducedness, nontrivial valuation or nonzero-algebra
hypothesis is introduced here.

## Equality of full bounded restrictions

`subatlas_domainChartRestriction` takes any two selected original charts,
any full domain `U` of the first, and an inclusion of its ambient image in
the second chart. The selected atlas and original atlas construct possibly
different finite common-chart choices. Their entire bounded maps from the
second chart algebra to `U.algebra` are nevertheless equal.

The proof uses the selected atlas's `domainImageChartCover`. For an arbitrary
algebra element, its actual finite full-domain cover separates equality.
On each component, the selected glued chart restriction equals its local
restriction by `restriction_comp_glueChartRestriction`; the original atlas's
`domainChartRestriction_test` identifies the same local map with the original
chart restriction. This comparison takes place on arbitrary algebra
elements, rather than only on values of spectrum points.

`subatlas_domainRestriction` treats arbitrary full domains `U` and `V`
in selected charts, with `U`'s ambient locus contained in `V`'s. It applies
`eq_domainRestriction_of_over_base`: the target domain's full universal
property cancels its structural map. The preceding chart comparison and
`domainRestriction_comp_baseMap` verify the required equation. Consequently
the selected and original restrictions are equal as bounded algebra maps
from `V.algebra` to `U.algebra`.

## Actual local-domain functor

`subatlasLocalDomain` forgets only the proof that the chart index satisfies
`P`. It keeps the full domain itself. The recorded algebra, locus and
ambient-map equalities are definitional.

`subatlasLocalDomainFunctor` sends each selected local domain to this
original local domain. Each arrow is the original local-domain inclusion
constructed from the same ambient subset proof. The identity and composition
laws follow from uniqueness in the actual local-domain inclusion Hom types.
`subatlasLocalDomainFunctor_map_restriction` separately proves that every
image arrow has exactly the input arrow's entire bounded restriction, using
`subatlas_domainRestriction` and the arrow's `restriction_eq` law.

`fullyFaithfulSubatlasLocalDomainFunctor` constructs a preimage of each
original inclusion by its same subset proof. Both inverse equations follow
from inclusion uniqueness. It supplies the `Full` and `Faithful` instances.
This comparison is of the local-domain inclusion categories; the full
bounded map identity is the stronger, separate assertion just proved.

## Presented-affinoid diagram

`subatlasLocalDomainAffinoidNatIso` has source the selected-to-original
functor followed by the original `LocalDomain.toAffinoidSpace`, and target
the selected atlas's own `LocalDomain.toAffinoidSpace`. Its component on
`U` is the identity isomorphism of `Opposite.op U.algebra`. Naturality is
`subatlasLocalDomainFunctor_map_restriction` transported through
`Quiver.Hom.op`. These diagrams use the opposite category of actual
presented affinoid algebras with bounded homomorphisms, so the isomorphism
retains the entire algebra data, including nonreduced information.

## Scope

The results compare all local-domain presentations and restrictions that
already have selected parents. They do not yet recognize an arbitrary old
domain through finitely many selected charts, construct its compatible
overlap diagram, or prove recognition invariance. Maximal-atlas uniqueness,
unrestricted analytic morphism comparison, etale sites and the Harris
tower specialization remain further obligations of the host task.
