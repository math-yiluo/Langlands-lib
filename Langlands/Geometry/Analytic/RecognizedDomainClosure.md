# Recognition and actual local-domain closure of the full atlas

Author: Worker 36.

This module constructs a recognized chart for every full affinoid domain
inside a chart of the full recognition atlas. It retains the literal
ambient domain locus, constructs a bounded equivalence from the given
domain algebra to the newly recognized finite Tate presentation, and
identifies the new chart with the original domain chart through that
equivalence. Consequently, every actual local full domain of the full
recognition atlas is already one of its chart ranges.

The source motivation is Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), the special-cover equalizer following
Lemma 1.2.12, printed p.20 / PDF p.17; the three recognition conditions
and Proposition 1.2.13(ii)–(iii), printed p.21 / PDF p.18; and the contained
affinoid domains and induced atlases after Definition 1.3.1, printed p.23 /
PDF p.20. Registered source `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These original pages were read for this construction. No source-specific
errata file was found in the available project and Library locations.

This is a derived local-domain closure construction. The proof uses the
actual finite local pieces, full-domain pushout overlaps, constructed
finite affinoid realization and proved completed-tensor admissibility.
It supplies the geometric inputs to the existing recognition-transfer
construction; it does not assume specialness, a realization or recognition
of the domain as an extra hypothesis. The source's broader assertions
about equivalent nets and iteration of recognition are not asserted here.

Two general comparison lemmas first record the exact canonical maps.
Let `W : a.SpecialSubset`, let `d` be finite gluing data with
`d.locus = W.val`, and let `c : d.AffinoidRealization`.
`realizationSectionEquiv_spectrumMap` proves that the spectrum
homeomorphism of the constructed bounded parent/sections equivalence
sends the existing `W.spectrumMap x` to the actual parent point
corresponding to the same literal point `x`. The proof combines the
defining-cover comparison formula with the exact canonical-map formula
of the finite realization and cancels the constructed homeomorphisms.

`chart_affinoidRealization` allows any intrinsic affinoid witness `h`
for `W.SectionAlgebra` and any bijectivity proof for the existing canonical
map. Put

```text
e = (W.realizationSectionEquiv d hd c).trans h.presentationEquiv.symm.
```

Then the new chart at a point `x` of `h.presentation` is exactly
`c.chart (e.spectrumHomeomorph x)`. The proof applies the preceding
canonical-point identity to the inverse recognized coordinate map and
uses the inverse identity of the parent's locus homeomorphism. Allowing
any witness matters because the recognition predicate subsequently
chooses its own intrinsic presentation.

Now fix `V : a.saturatedAtlas.RecognizedSubset` and
`D : Domain K V.algebra`. The existing
`fullRecognitionDomainSpecialSubset V D` has literal locus
`V.domainLocus D`, and its finite gluing data has an actual realization
with parent `D.algebra`. Its special covering already has proved
admissible genuine completed-tensor overlap maps.
`fullRecognitionDomainSpecialSubset_isRecognized` applies the existing
recognition-transfer theorem to these constructed data and obtains all
three intrinsic conditions:

- the unchanged canonical section algebra is intrinsically affinoid;
- its existing canonical spectrum map is bijective;
- a genuinely special defining cover consists of full represented
  affinoid domains in the constructed presentation.

`fullRecognitionDomainRecognizedSubset` bundles this proof and the
literal special subset. Its locus theorem is the literal equality with
`V.chart '' D.locus`. The finite-cover witnesses, component bounded maps
and all-test universal properties come from the preceding constructions.
No output chart or section comparison is supplied.

`fullRecognitionDomainAlgebraEquiv` constructs the bounded equivalence
from `D.algebra` to this recognized subset's actual algebra. It composes
the previously constructed parent/sections equivalence with the inverse
of the recognition witness's presentation/sections equivalence.
Both directions are actual bounded algebra maps with proved inverse
identities; this comparison does not identify algebras merely because
their spectra agree.
`fullRecognitionDomainRecognizedSubset_chart` applies the general
comparison lemma to identify the newly recognized chart exactly:

```text
new.chart x =
  V.domainAmbientMap D
    ((a.fullRecognitionDomainAlgebraEquiv V D).spectrumHomeomorph x).
```

For `U : LocalDomain a.fullRecognitionAtlas`,
`fullRecognitionAtlas_localDomain_chart_range` applies the new construction
to its actual index and full domain. The resulting index belongs to the
same full recognition atlas, and its chart range is exactly `U.locus`.
`fullRecognitionAtlas_localDomainFamily` therefore proves

```text
a.fullRecognitionAtlas.localDomainFamily =
  range (fun i => range (a.fullRecognitionAtlas.chart i)).
```

One inclusion uses these newly constructed recognized indices; the
other uses each original chart as its own whole full domain. This is
literal closure under every local full domain, stronger than a statement
of mutual local refinement. It is not an equality with the smaller
original input chart family.

The coefficient-field, ambient-space and original-index universes remain
independent. The field is complete and ultrametric and may have trivial
valuation. The ambient space need not be Hausdorff. No nonzero-algebra,
reducedness or nonempty-cover premise is added. Imported representations
retain their full universal properties against all presented affinoid
test algebras.

The construction does not invoke the general special-intersection lemma,
closed-ideal effectiveness or Kiehl descent as an assumed new input.
It proves local full-domain closure of the constructed full atlas, while
equivalent-net invariance, iteration of recognition, maximal-atlas
uniqueness and the unrestricted morphism-category identification remain
separate obligations. Analytic étale and equivariant sites and the Harris
tower specialization also remain outside this unit.
