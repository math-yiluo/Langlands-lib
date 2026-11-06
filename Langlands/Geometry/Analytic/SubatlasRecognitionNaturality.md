# Full bounded naturality of selected-atlas domain recognition

Author: Worker 36.

The constructed recognition of every original local full domain through
a locally refining selected atlas commutes with every original
local-domain inclusion on the entire bounded algebra maps. This gives
an actual recognition functor and a natural isomorphism between its
affinoid diagram and the original local-domain diagram, over the same
ambient space.

## Source and provenance

This is derived infrastructure for Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), Proposition 1.2.13(i)–(ii),
printed p.21 / PDF p.18. Registered source:
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The original page was read for this construction. No source-specific
errata file was found in the available Library location.

Part (i) compares completed domain families under passage to a subnet.
Part (ii) constructs the extended atlas and its canonical bounded
restriction maps. The present module establishes full bounded
naturality for the specific old-local-domain recognition constructed
in `SubatlasDomainRecognition`. It uses finite full-domain separation
and the generic realization recovery theorem in
`FullRecognitionNaturality`. The functor and natural isomorphism below
are derived internal constructions; they are not names or independent
assertions appearing verbatim in the source.

## Recovery on every contained selected-saturation chart

Write `b = a.subatlas P hP`, with
`hP : a.IsLocallyRefiningSelection P`. For a selected finite chart cover
`c : a.SelectedChartCover P parent` and an actual full domain
`U : Domain K (a.algebra parent)`, let `d` and `r` be the finite
gluing datum and its unchanged-old-algebra realization constructed
earlier. Every `b.saturatedAtlas` chart `s` contained in the old
domain's literal locus has its canonical actual full component over
`U.algebra`, denoted `a.subatlasSaturatedComponent P hP ⟨parent, U⟩ s hs`.

`SelectedChartCover.saturatedDomain_originalRestriction` proves
that `d.originalRestriction s` composed with `r.restrictFromParent`
is exactly this component's entire bounded structural map. This
applies to every contained chart, including charts outside the
defining finite family.

The proof gives `d.locus` its Hausdorff topology using `r.locusHomeomorph`
from the old affinoid spectrum. It constructs a finite subordinate
full-domain cover of `s` with `d.subordinateCoverOfHausdorff`.
The cover's `algebra_ext_of_restrict_eq` separates arbitrary elements
of `s.algebra`. On each child, `d.original_comp_originalRestriction`
identifies the equalizer restriction with its defining-component
restriction, while `subatlasSaturatedComponent_naturality` identifies
the two canonical old-domain components with that same bounded
composite. Evaluating these whole-map equations proves equality on
the arbitrary algebra element being separated.

`SelectedChartCover.saturatedDomainAlgebraEquiv_originalRestriction`
combines this equality with the generic
`RecognizedSubset.originalRestriction_comp_affinoidRealization`
theorem. Restriction from the constructed recognized presentation
after the constructed old-algebra equivalence is thus the same
canonical full component map for every contained `s`.
`subatlasRecognizedLocalDomainEquiv_originalRestriction` states this
for every `U : LocalDomain a`, using the finite selected cover already
constructed from `hP`.

## Entire bounded naturality

For an actual inclusion `f : U ⟶ V` in `LocalDomain a`,
`subatlasSaturatedComponent_comp_restriction` proves that the
component over `U` composed with `f.restriction` equals the component
over `V`. The two actual original local-domain inclusions from the
forgotten selected representative to `V` are equal by the proved
uniqueness of `LocalDomain.Inclusion`. Projecting their restriction
maps gives the asserted complete bounded-map equation.

Let `F(U) = a.subatlasRecognizedLocalDomain hP U`, and write
`e_U : U.algebra ≃ F(U).algebra` for the constructed bounded
equivalence. `subatlasRecognizedLocalDomainEquiv_naturality` proves
for every `f : U ⟶ V`:

```
e_U.comp f.restriction = (F(U).restriction F(V) f.subset).comp e_V.
```

The proof separates arbitrary elements by the actual finite
`F(U).componentCover`. Each component's structural map equals its
canonical original-chart restriction. On every such component, the
recovery theorem just proved, the original-domain inclusion
composition law, and the recognized original-restriction composition
law identify the two sides. This retains all algebra elements,
including nilpotents; spectrum-point agreement is not used to infer
equality of bounded maps.

## Recognition functor and affinoid natural isomorphism

`subatlasLocalDomainRecognitionFunctor` has source `LocalDomain a`
and target `b.saturatedAtlas.RecognizedSubset`. Its object map is
the constructed `F`. Its arrow map uses each inclusion's unchanged
literal subset relation. The functor laws hold in these thin
inclusion categories.

`subatlasLocalDomainRecognitionAffinoidIso U` has source
`Opposite.op F(U).algebra` and target `Opposite.op U.algebra`.
Its forward arrow is the opposite of `e_U.toBoundedAlgHom`, and
its inverse is the opposite of the bounded inverse. The two inverse
laws are proved by bounded-map extensionality and the actual
equivalence inverse laws.

`subatlasLocalDomainRecognitionAffinoidNatIso` assembles these
components into

```
subatlasLocalDomainRecognitionFunctor ⋙
  RecognizedSubset.toAffinoidSpace b.saturatedAtlas
  ≅ LocalDomain.toAffinoidSpace a.
```

Naturality is precisely the opposite of the full bounded equation
proved above. Finally,
`subatlasLocalDomainRecognitionAffinoidNatIso_over_ambient` applies
the affinoid spectrum functor to a component and identifies its
composite with `U.ambientMap` with the constructed recognized chart.
It uses the earlier exact chart-recovery theorem.

## Hypotheses and remaining scope

The field is a complete ultrametric normed field and may have trivial
valuation. The field, ambient space and original index universes are
independent. The ambient space has its topology and actual atlas.
The only selection hypothesis is the explicit local refinement
condition. No global Hausdorffness, reducedness, nonzero-algebra or
nonempty-cover premise is added. Full-domain universal properties
retain all presented affinoid test algebras and finite positive
polyradii.

This unit supplies full naturality and the affinoid-diagram natural
isomorphism for original local full domains. Arbitrary recognized
subsets of the original and selected saturated atlases, their
category equivalence, arbitrary equivalent-net invariance,
maximal-atlas uniqueness, unrestricted analytic morphism comparison,
analytic etale and equivariant sites, and Harris specialization
remain subsequent obligations.
