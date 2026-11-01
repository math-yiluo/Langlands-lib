# Retaining exactly the nonempty original atlas charts

Author: Worker 56.

This is an internal construction from `AtlasSubatlas` and the existing category
of complete chosen bounded atlas maps. It introduces no external mathematical
premise. Its purpose is to prepare disjoint sums of atlases whose component
atlases may have overlapping charts. An indexed atlas identifies chart indices
by their actual domains; two empty domains in different components would violate
that injectivity requirement.

Throughout, `K` is a complete normed ultrametric field. The space and chart index
universes are independent. No nonemptiness of the underlying space, reducedness
of an algebra, or restriction to strict polyradii is assumed.

## The same-space atlas

For an indexed atlas `a`, `NonemptyChart i` is the proposition
`Nonempty (BanachSpectrum (a.algebra i))`. It is a condition on the original
algebra, with no replacement of that algebra. `HasNonemptyCharts` says that this
condition holds for every original index; an atlas with no indices can satisfy
it on an empty space.

`nonemptyCharts_locallyRefining` proves the relative local refinement required
by the selected-subatlas construction. Given a point in an original chart, its
preimage in that chart witnesses that the chart has nonempty spectrum. The
singleton consisting of the same chart domain is then a finite selected family,
contains the point, lies inside the original chart, and has union a relative
neighborhood of that point. The obligation on an empty chart is vacuous.

`nonemptySubatlas` selects precisely these original indices. The imported
subatlas construction retains the underlying space and topology, every surviving
original algebra and chart embedding, and the original bounded restrictions,
including their chart equations, universal factorization, identities and
composition laws. Its net condition follows from the proved relative local
refinement. `nonemptySubatlas_hasNonemptyCharts` records the witness attached to
each surviving index.

`nonemptyPresentation` applies this construction to a bundled presentation.
`nonemptyInclusion` is an actual chosen atlas arrow back to the original
presentation: its continuous base map is the identity, its index map forgets
the nonemptiness witness, and its pullback at every surviving chart is the bounded
identity on the original algebra.

## Complete maps and actions

For every actual chosen atlas arrow `f : A ⟶ B`, `Hom.nonemptyChart_target`
proves that the selected target chart of a nonempty source chart is nonempty.
It applies `BanachSpectrum.comap` for the original bounded algebra pullback to
a source spectrum point. Thus no surjectivity or separation assumption on
spectrum points is used.

`Hom.nonemptyMap` restricts `f` to the two nonempty presentations. Its base map
is exactly `f.baseMap`; its index at `i` is `f.indexMap i.val` with the preceding
nonemptiness witness; its bounded pullback is exactly `f.pullback i.val`.
Monotonicity, chart commutation and restriction commutation are the corresponding
original laws. The three displayed projection lemmas record these exact data.

`Hom.nonemptyMap_id` and `Hom.nonemptyMap_comp` compare the entire arrows,
including dependent bounded pullback families, by the existing `Hom.ext`.
They give the endofunctor `nonemptyFunctor` on
`AffinoidAtlasPresentation.{u,v,w} K`. The equation
`Hom.nonemptyMap_nonemptyInclusion` proves naturality of the canonical
inclusions, packaged as `nonemptyInclusionNat`. The exact equality
`nonemptyFunctor_spaceFunctor` says that composing this functor with the
underlying-space functor changes neither objects nor continuous maps.

Under the explicit hypothesis `A.atlas.HasNonemptyCharts`, `nonemptyInv` sends
every original index to itself with its nonemptiness witness, and uses the
identity base map and bounded identity pullbacks. Complete-arrow extensionality
proves both inverse laws for `nonemptyIso`. An inverse is not constructed for an
arbitrary presentation that has an empty original chart.

For every monoid `M`, `nonemptyActionFunctor` uses the functorial action
construction to restrict categorical `M`-actions and equivariant complete
arrows. `nonemptyActionInclusion` is an equivariant arrow to the original action;
its commutation equation is the already proved naturality of the inclusion,
applied to each original action arrow. This statement concerns categorical
actions and introduces no topological continuity convention for `M`.

## Scope

This construction deletes empty original charts on exactly the same space.
It does not identify chosen atlas arrows modulo refinement or construct a
localization, general analytic category, induced action on an arbitrary source
atlas, analytic adjunction, or analytic site. Those constructions remain
separate obligations. All equalities of algebra maps here compare the actual
bounded maps; none is inferred from equality on spectrum points.
