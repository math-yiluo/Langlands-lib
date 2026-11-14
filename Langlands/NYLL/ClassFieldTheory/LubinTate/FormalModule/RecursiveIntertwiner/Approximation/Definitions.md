# NYLL M353.002: bundled approximations

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`.
The readable pinned source is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`.
Its file SHA-256 is `627cad1b4ca585bb98d54d4dc97a88735e737576155b62e00476e824862983f6`.
The registered source `nyll-classfieldtheory-fbd320cd-supplement` has content
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`;
the snapshot collection is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
No applicable NYLL erratum was found in the current Library's `notes/errata/`.

The source-private abbreviation `LubinTate.SameUniformizer.Approximation`,
lines 46–48, is published as `Langlands.NYLL.PortInternal.M353.d002`.
It is exactly the subtype
`{H : MvPowerSeries sigma F.valuationSubring // HasLinearTerm H L}`.
The prescribed coefficients `L : sigma → F.valuationSubring` are explicit.
The parameters `{K : Type u} [Field K] {F : LocalField.{u, v} K}` and
`{sigma : Type w} [Fintype sigma]` are implicit, with all three source
universes retained. No uniformizer, uniformizer witness or Lubin–Tate series
is a parameter; the unused source section variable `pi` is omitted.

`HasLinearTerm H L` is the published predicate saying that
`H - linearForm L` has total order at least two. `LocalField` is the shared
adapted package extending the published `CompleteDVF`, with finite residue
field. This abbreviation reuses that package, its actual valuation subring,
and the published arbitrary-commutative-ring linear-term definitions.
It does not introduce a competing local-field or power-series interface.

Worker 331 extracted the abbreviation, replaced its private name by the
required port-internal name, prefixed opened namespaces by `Langlands.NYLL`,
and added a docstring. Its body and effective source binders are unchanged.
The noncomputable section and universe declarations are retained. The original
imports are replaced by the focused published LocalField and LinearTerm
Definitions modules; unrelated declarations and the module overview are
omitted, and a focused overview and modification notice are added.
The focused Lean check verifies that no DegreeStabilization or
RecursiveCorrection import is needed. The abbreviation's body does not use
M353.001's theorem, so it can be published before that theorem's exact proof.
No theorem or nonemptiness assertion is included in this data unit.

The original 2026 copyright, Apache-2.0 release and author header are
retained verbatim. Existing `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain unchanged. No patch10 edit affects this source module.
