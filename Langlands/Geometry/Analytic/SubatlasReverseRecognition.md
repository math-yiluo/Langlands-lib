# Reverse recognition under locally refining subatlas selection

This internal construction transports a recognized subset of the saturated
selected atlas to a recognized subset of the saturated original atlas. It
retains the literal ambient locus and constructs a bounded comparison of the
actual algebras and an equation recovering the ambient chart.

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), the special-cover definition on printed page 20 (PDF page 17) and
the recognition criterion and Proposition 1.2.13(ii) on printed page 21
(PDF page 18). The implementation is derived infrastructure for invariance of
recognition under locally refining selection, using the Library's full
affinoid-domain universal properties.

Let `a` be an indexed affinoid atlas over a complete ultrametric normed field
`K`, let `P` be a locally refining selection of its charts, and write
`b = a.subatlas P hP`. The ambient and original index universes are independent.
The input `V` is any recognized subset of `b.saturatedAtlas`. There is no input
recognition witness relative to `a.saturatedAtlas` and no supplied comparison
of the two section algebras.

For a selected saturated index `s`, the existing
`subatlasSaturatedOriginalIndex` forgets the selection proof on its actual
local-domain representative and takes the corresponding literal locus as an
original saturated index, denoted `S(s)`. Its original and selected chart
ranges agree. The new `subatlasSaturatedOriginalEquiv` constructs

```text
e_s : b.saturatedAtlas.algebra s ≃ a.saturatedAtlas.algebra S(s)
```

as a bounded algebra equivalence using the actual mutually inverse
local-domain inclusions. Its spectrum homeomorphism has the contravariant
direction from the original saturated spectrum to the selected one.
`subatlasSaturatedOriginalEquiv_over_ambient` proves that this map commutes
with the unchanged ambient charts.

For every containment of selected saturated chart ranges `s ⊆ t`,
`subatlasSaturatedOriginalEquiv_naturality` proves the equality of entire
bounded algebra maps

```text
r_original(S(s), S(t)) ∘ e_t = e_s ∘ r_selected(s, t).
```

The two composites come from arrows between the same actual original
local-domain presentations. Full universal-property uniqueness identifies
these arrows. The existing full restriction comparison for the subatlas
forgetful functor then gives the displayed equation. Equality of maps is not
inferred from their values on spectrum points.

For every selected saturated chart `s` contained in `V.locus`,
`subatlasReverseChartDomain` constructs a full domain over the unchanged
`V.algebra`. Its algebra is the original saturated presentation at `S(s)`,
its bounded structural map is
`e_s ∘ V.originalRestriction s`, and its literal locus is the inverse image
under `V.chart` of the original saturated chart range. The full representation
is transported by `Represents.postcomp_equiv`. The corresponding ambient
chart equation follows from the original recognized restriction equation and
the proved equation for `e_s`. Naturality of these full structural maps
follows by composing the displayed comparison equation with the original
recognized restrictions.

`subatlasReverseRecognitionGluing` transports the finite cover chosen by
`V.property.cover` and every one of its overlap indices through `S`.
Equality of chart ranges proves the full intersection equations and equality
of the finite union with `V.locus`. No new finite-cover extraction or
Hausdorff assumption on the ambient space is needed.
`subatlasReverseRecognitionAffinoidRealization` uses exactly `V.algebra`
and `V.chart`, the transported full domains, and their entire bounded
naturality equations for overlap compatibility.

The generic finite-realization construction in
`AffinoidRealizationSpecialCover` now proves specialness of this transported
cover, including Hausdorffness of its literal union and admissibility of the
genuine completed-tensor overlap maps. It also constructs all three intrinsic
recognition conditions. Applying it defines
`subatlasReverseRecognizedSubset`, whose locus is proved equal to `V.locus`.
The final bounded equivalence and chart equation are

```text
subatlasReverseRecognizedSubsetEquiv :
  V.algebra ≃ (subatlasReverseRecognizedSubset hP V).algebra

(subatlasReverseRecognizedSubset hP V).chart x =
  V.chart (subatlasReverseRecognizedSubsetEquiv.spectrumHomeomorph x).
```

Both directions of the algebra equivalence are constructed through the actual
canonical section algebras and finite full-domain descent. The result includes
nonreduced algebras, trivial valuations, arbitrary positive polyradii and empty
finite families; no exclusion of these cases is imposed.

This unit establishes reverse recognition and algebra/chart recovery for a
locally refining selected subatlas. Full naturality of the reverse recognized
restriction maps, the two-sided recognized category equivalence, arbitrary
equivalent-net invariance, maximal-atlas uniqueness and the analytic and
equivariant site constructions remain separate work. It does not claim the
whole of Proposition 1.2.13 or completion of the Harris analytic foundations.
