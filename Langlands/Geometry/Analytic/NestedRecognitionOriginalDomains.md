# Canonical original-chart domains through nested recognition

Author: Worker 36.

This module constructs canonical full domains for contained original
charts inside a recognized chart of the saturated recognition atlas.
Every domain retains the unchanged original chart algebra. Its structural
map composes three actual bounded restrictions, recovers the original
ambient chart and satisfies full algebraic naturality for every nested
pair of original charts.

The source motivation is Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), the recognition construction and
Proposition 1.2.13(ii)–(iii), printed p.21 / PDF p.18. Part (ii)
constructs canonical bounded restrictions in the extending affinoid atlas;
part (iii) compares successive recognition stages using finite defining
covers. Registered source `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
This original passage was read for the construction. No source-specific
errata file was found in the available project and Library locations.

This is a derived map-construction step for nested recognition. It uses
the actual original-domain maps in recognized presentations and the
actual local-domain comparison maps after saturation. Full naturality
is proved from their algebraic structural equations. The result does not
infer equality of bounded maps from agreement on spectrum points, and
does not yet prove idempotence of recognition.

Fix an arbitrary indexed affinoid atlas `a`, put
`B = a.recognitionAtlas`, and take an original index `s : a.Index`.
`recognitionOriginalLocalDomain s`, denoted `Lₛ`, is the actual whole
local-domain presentation of `a.originalRecognitionIndex s` in `B`.
Its locus is exactly `range (a.chart s)`. Its algebra is the presentation
constructed by recognition for that original chart.

`recognitionOriginalDomain s`, denoted `Pₛ`, applies the existing full
original-chart domain construction in this recognized presentation.
Its algebra is literally `a.algebra s`, and its base map `pₛ` is the
canonical original restriction from the recognized algebra. It retains
the full domain universal property against every presented affinoid
test algebra.

`recognitionOriginalSaturatedIndex s`, denoted `Tₛ`, uses the actual
literal locus of `Lₛ` as an index of `B.saturatedAtlas`. Its range theorem
recovers exactly the original `a.chart s` range.
`recognitionOriginalToSaturated s`, denoted `qₛ`, is the canonical
equal-locus local inclusion from `Lₛ` to the representative chosen for
`Tₛ`. It is obtained from the actual local-domain isomorphism on equal
loci, whose maps are entire bounded restrictions.

`recognitionOriginalSaturatedDomain s` first regards `qₛ` as a full
domain over its target representative algebra and then extends `Pₛ`
through it. This constructs a full domain over the saturated chart
algebra, still with the unchanged algebra `a.algebra s`.
Its structural map is `pₛ.comp qₛ.restriction`.
The ambient recovery theorem composes the actual inclusion's ambient
naturality with the whole-domain chart identity and the original-domain
chart formula. Thus the constructed domain recovers the original
`a.chart s`, including its exact map on every spectrum point.

For an original inclusion `range (a.chart s) ⊆ range (a.chart t)` and an
actual local inclusion `f : Lₛ ⟶ Lₜ`,
`recognitionOriginalDomain_restriction` proves

```text
pₛ.comp f.restriction =
  (a.restriction s t hst).comp pₜ.
```

The existing whole-local-domain restriction theorem first recovers the
actual recognized inclusion restriction stored by `f`. The theorem
comparing original restrictions with recognized restrictions and the
original-atlas naturality theorem then give this equality of complete
bounded maps. The proof evaluates the full map equalities on arbitrary
algebra elements, so it retains nonreduced algebraic information.

Now take `W : B.saturatedAtlas.RecognizedSubset` and suppose
`range (a.chart s) ⊆ W.locus`.
`recognitionChartOuterDomain W s hs` is the actual original full domain
of the saturated chart `Tₛ` in `W.algebra`.
`recognitionChartDomain W s hs` extends the already constructed
`recognitionOriginalSaturatedDomain s` through this outer domain.
It is therefore a full domain over `W.algebra` with algebra literally
`a.algebra s`. Its base-map theorem records the entire composite

```text
(pₛ.comp qₛ.restriction).comp (W.originalRestriction Tₛ ...).
```

`recognitionChartDomain_over_ambient` composes the two full-domain
spectrum maps and applies their actual ambient formulas to recover
`a.chart s`. `recognitionChartDomain_locus` proves that the full domain's
locus is exactly `W.chart ⁻¹' range (a.chart s)`. It uses the full range
identity for the forward direction, and injectivity of the actual
recognized chart for the reverse direction.

`recognitionChartDomain_naturality` proves that these canonical maps
commute with every entire original restriction. If `rₛ` and `rₜ` denote
their base maps, its conclusion is

```text
(a.restriction s t hst).comp rₜ = rₛ.
```

The proof constructs the actual local inclusion `f : Lₛ ⟶ Lₜ` and the
saturated inclusion `g : representative Tₛ ⟶ representative Tₜ`.
Full local-domain uniqueness identifies `f ≫ qₜ` with `qₛ ≫ g`, giving
the full bounded square equation. The preceding theorem identifies
`pₛ.comp f.restriction` with the original restriction followed by `pₜ`.
Naturality of `W.originalRestriction` identifies
`g.restriction.comp W.originalRestriction Tₜ` with
`W.originalRestriction Tₛ`. Composing these three entire equations
proves the result. Spectrum points play no role in proving algebra-map
naturality.

Applying this generic construction with `a` equal to a first saturated
atlas provides coherent original-chart maps for a chart of the iterated
full recognition atlas. The existing finite refinement supplies original
chart loci covering such a chart; this module supplies canonical full
maps with the bounded naturality needed to construct its overlaps.
It does not assert that an arbitrary family of full maps with the same
spectral images is compatible.

The coefficient-field, ambient-space and original-index universes are
independent. The complete ultrametric field may have trivial valuation.
There is no ambient Hausdorff, nonzero-algebra, reducedness or
nonempty-cover premise. All domains and inclusions are the actual
constructed full representations.

This unit supplies canonical full original-chart domains and their
complete restriction naturality through the nested atlases. Finite
overlap construction, completed-tensor specialness for the flattened
cover, recognition idempotence, equivalent-net invariance and maximal
atlas uniqueness remain later obligations. The general
special-intersection lemma and closed-ideal effectiveness are not
assumed.
