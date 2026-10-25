# Residue nonvanishing and the full trivialization locus

The theorem `Langlands.SchemeModule.lineBundleSectionResidueComparison`
proves the published proposition `LineBundleSectionResidueComparison.{u}`.
It applies to every scheme `X : Scheme.{u}`, actual locally free rank-one
bundle `L : LineBundle X`, and global section `s : GlobalSections L.obj`.
It establishes both the pointwise equivalence
`NonvanishingAt L.obj s x ↔ IsStalkFrame L.obj s x` and the equality

```text
nonvanishingLocus L.obj s = (trivializationOpen L.obj s : Set X).
```

The nonvanishing predicate retains its published meaning: pull back the
section morphism along `X.fromSpecResidueField x`, precompose with the inverse
canonical structure-module comparison, evaluate at one, and require the
resulting section to be nonzero. There are no additional compatibility,
affineness, quasi-compactness, or separation hypotheses.

The helper theorem `lineBundleResidueOpenComparison` proves the second
component. The published `lineBundle_stalkFrame_set_eq` rewrites the
underlying set of the trivialization open as the entire set of stalk frames.
Set extensionality then reduces the desired equality to the pointwise
equivalence supplied by the published `lineBundleResidueStalkCriterion`.
The final theorem pairs that pointwise criterion with this set equality.
Thus the open-locus result concerns the whole nonvanishing set, with no
remaining interior operation.

This is an internal derived proof assembled from unchanged Library results.
`SectionResidueStalkProof`, assembled by Worker 149 using Worker 311's chart
and stalk argument, proves the actual residue comparison using Worker 354's
published local-chart theorem and the scalar residue criterion.
`LineBundleFrameOpen`, by Worker 311, proves the openness and full
stalk-frame set equality by extending a scalar inverse germ to a neighborhood
and applying the general-module interior comparison. The present module
imports those proofs by Lean name and performs only the final set comparison
and conjunction construction. The original proposition and all definitions
it depends on are unchanged.
