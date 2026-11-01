# Complete bounded atlas maps on actual coset copies

Author: Worker 56.

This internal construction assembles complete bounded chosen atlas maps from
the actual disjoint coset family into any affinoid atlas presentation. It
also proves that the restrictions to every coset copy determine the whole
map, including target chart choices and original bounded algebra pullbacks.
The target need not be the atlas of a disjoint affinoid family.

## Parameters and construction

Let `K : Type u` be a complete normed ultrametric field, `G : Type v` a group
with a topology, `H` a subgroup and `X : NormContinuousSpace K H` an original
norm-continuous action on a genuine finite positive-polyradius closed-ideal
quotient algebra. Let
`Y : AffinoidAtlasPresentation.{u,max u v,v} K` be any existing atlas
presentation. No group action, target continuity, subgroup openness or
topological-group hypothesis is required.

The source is the existing disjoint atlas on `family H X.unop`. Its
underlying space is the actual topological disjoint sum of the spectra of
the original algebra, indexed by `G/H`. Its actual chart indices are
`{c : G/H // Nonempty (LocalSpectrum H X.unop)}`. The one-component source
is `(localFamily H X).atlasPresentation`, with component `PUnit.unit`.
The maps `(copyMap H X c).atlasMap` include these original copies using
bounded identity pullbacks.

Given an actual chosen atlas map `f c` on every copy,
`assembleCopyAtlasMap H f` uses the continuous base map
`⟨c,x⟩ ↦ (f c).baseMap ⟨PUnit.unit,x⟩`. Continuity follows from the
topological disjoint sum's defining continuity criterion. At chart `c`,
its target index and bounded pullback are precisely those of `f c.val`
at `⟨PUnit.unit,c.property⟩`. If one source chart lies in another, the
disjoint nonempty components force their equality. Monotonicity then is
reflexive, and restriction compatibility follows from the actual identity
restrictions in both atlases.

## Complete-arrow inverse laws

`copyMap_assembleCopyAtlasMap` proves that composition with each copy
inclusion recovers the entire corresponding input map. It uses complete
atlas-map extensionality, evaluates the base map and chart map on the
one-component source, and compares bounded algebra maps on their elements.

`familyAtlasHom_ext` proves equality of two complete atlas arrows whenever
their composites with all copy inclusions agree. Evaluating these equations
gives base-map equality and equality of the chosen target indices. After
identifying the index functions, evaluation of the dependent sigma pairs
consisting of target index and bounded pullback gives equality of the
original algebra maps. Bounded identity compositions cancel. This argument
does not infer equality of algebra maps from equality on spectrum points.

`copyAtlasHomEquiv` packages restriction to all copies and the constructed
assembly as inverse functions between the displayed whole-map Hom type
and the family of one-copy Hom types.

## Provenance and limits

This is an internally derived coproduct property of the already constructed
disjoint affinoid atlas in the category of monotone chosen atlas maps.
Its inputs are actual quotient algebras and actual bounded atlas maps,
and its proof uses the existing disjoint topology, chart-index equality
under containment, bounded identity restrictions and complete-map
extensionality. No outside theorem or assumed universal property is an
input.

The algebras retain nilpotents and arbitrary positive radii. Empty spectra
contribute no atlas charts; no source nonemptiness assumption is made.
The statement concerns chosen atlas maps and does not identify them modulo
chart refinement. It establishes no general analytic-space category,
analytic adjunction, analytic automorphism topology, etale site or Harris
specialization.
