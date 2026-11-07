# Full bounded naturality of selected recognition of recognized subsets

Author: Worker 36.

The selected recognition construction preserves every bounded restriction
between original recognized subsets. This module proves recovery of the
restriction to every contained selected saturated chart and constructs a
natural isomorphism of the entire presented-affinoid diagrams, compatible
with their maps into the unchanged ambient space.

## Source and provenance

This is derived infrastructure for Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), Proposition 1.2.13(i)–(ii),
printed p.21 / PDF p.18. Registered source:
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The original page was read during this development; no source-specific
errata file was available in the Library notes.

Part (i) compares completed domain families under passage to a subnet;
part (ii) constructs the canonical bounded restrictions in the extended
atlas. The present module establishes full bounded naturality for the
original-to-selected recognition construction under an explicit local
refinement hypothesis. Its algebra presentation comparisons and categorical
packaging are derived implementation infrastructure. The proof uses
finite subordinate covers and separation by full-domain restrictions,
rather than faithfulness of spectrum maps.

The inputs are an indexed affinoid atlas `a`, a selection `P` and its
proof `hP : a.IsLocallyRefiningSelection P`. Write `b = a.subatlas P hP`.
All recognized objects below are actual recognized subsets of the stated
saturated atlases, and all comparison equivalences are those constructed
in `SubatlasRecognizedRecognition`.

## Canonical maps and arbitrary original inclusions

For original recognized subsets `U ⊆ V` and a selected saturated chart
`s` contained in `U`,
`subatlasRecognizedChartDomain_comp_restriction` proves

```text
canonical(U,s).baseMap.comp (U.restriction V) = canonical(V,s).baseMap.
```

The canonical map is the original recognized restriction at the forgotten
selected chart, followed by its actual equal-locus comparison restriction.
The latter map is fixed independently of the recognized parent.
`RecognizedSubset.originalRestriction_comp_restriction` identifies the
entire original restrictions, and associativity of bounded composition
gives the displayed equation.

## Recovery at every contained selected chart

For an original recognized subset `W`, let `d` and `c` be its constructed
finite selected gluing datum and realization, respectively. For every
selected saturated chart `s` whose range lies in `W.locus`,
`subatlasRecognition_originalRestriction` proves that the section
algebra's canonical restriction to `s`, composed with
`c.restrictFromParent`, equals the canonical full-domain map from
`W.algebra` to the algebra at `s`.

The proof transports Hausdorffness from the parent Banach spectrum to
`d.locus`, then takes the finite subordinate cover of the chart `s`.
The cover's actual full-domain restrictions separate elements of its
algebra. On each covering domain, the finite section algebra's original
restriction equation and the proved canonical full-domain naturality
identify both composites with the same map into the covering algebra.
Thus all algebra elements agree, including nilpotents.

`subatlasRecognizedSubsetEquiv_originalRestriction` combines this result
with `RecognizedSubset.originalRestriction_comp_affinoidRealization`.
For the constructed equivalence `e_W` it proves

```text
(selectedRecognized(W).originalRestriction s).comp e_W = canonical(W,s).baseMap.
```

This holds for every contained selected saturated chart, not merely the
components of the finite realization chosen to construct `W`.

## Naturality and the actual affinoid diagram

`subatlasRecognizedSubsetEquiv_naturality` treats every original inclusion
`U.locus ⊆ V.locus`. With `Y` and `Z` their selected recognized
presentations, it proves the entire bounded-map equation

```text
e_U.comp (U.restriction V) = (Y.restriction Z).comp e_V.
```

The finite component domain cover of `Y` separates algebra elements.
On each component, the just-proved recovery formulas for `U` and `V`,
canonical-map compatibility with the original inclusion, and selected
recognized restriction composition identify both sides. The argument
uses full bounded maps throughout.

`subatlasRecognitionFunctor` sends an original recognized subset to its
constructed selected recognized presentation. It sends each inclusion to
the inclusion with the same literal containment, and its locus theorem is
definitional. `subatlasRecognitionFunctor_naturality` states the preceding
bounded equation for every categorical arrow.

`subatlasRecognitionAffinoidIso` uses `e_V` and its actual bounded inverse
to give an isomorphism between the selected and original objects in the
opposite category of presented affinoid algebras. The inverse identities
are proved from the two identities of the bounded algebra equivalence.
`subatlasRecognitionAffinoidNatIso` assembles these isomorphisms using the
full bounded naturality equation. Its source is the selected recognition
functor followed by the selected recognized affinoid-space functor; its
target is the original recognized affinoid-space functor.

`subatlasRecognitionAffinoidNatIso_over_ambient` applies the constructed
chart-recovery equation. It shows that the spectrum map of each natural
comparison, followed by the original chart, is exactly the selected
recognized chart in the original ambient space.

## Hypotheses and remaining scope

The field is complete and ultrametric, with trivial valuations allowed.
The field, ambient space and original atlas index have independent
universes. No global Hausdorffness, reducedness, nonzero-algebra or
nonempty-cover hypothesis is added. The finite covers and recognition
comparisons used in the proof are constructed, rather than input objects.

This module gives a functor and a natural isomorphism of its entire
actual affinoid diagram. Reverse recognition and a two-sided equivalence
of recognized inclusion categories remain subsequent work. General
equivalent-net invariance, maximal-atlas uniqueness, the analytic morphism
comparison, etale and equivariant sites, and the Harris specialization
remain obligations of the host task.
