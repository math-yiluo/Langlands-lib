# Finite principal-unit correction products (M132.020)

This is the unchanged recursive data construction for a sequence
`z : ∀ d : Nat, principalUnits K (n + d)`. Its complete telescope is
`(K : Type u) [Field K] [ValuativeRel K] (n : Nat)` followed by explicit `z`;
its codomain is `Nat → 𝒪[K]ˣ`. The zero-stage value is `1`; the successor value
is the previous value multiplied on the right by the underlying unit of `z d`.
It is the actual finite product, with no topology or limit included.

M132.020, source lines 307–311, maps
`LocalFieldTheory.principalUnitsCorrectionProduct` to
`Langlands.NYLL.LocalFieldTheory.principalUnitsCorrectionProduct`.
The recursive body, all binders, universe and equation patterns are unchanged.
The only mathematical dependency is the published `principalUnits`, imported
through `PrincipalUnits.Definitions`. The other source imports are omitted.
The namespace prefix and focused module documentation are the only remaining
changes. Source notation scope, universe, noncomputable section and `open Filter`
are retained. No constructor law or convergence assertion is proved here;
those have separate Prop targets. This definition adds no instance or host bridge.

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean`.
The complete source file SHA-256 is
`6147c6613cd0176ace8787d7c65a3026d23bd5e23dc3282902d5ea66a0977c83`.
Its readable retained copy is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the published errata notes.

The original copyright, Apache-2.0 license and author header are retained.
The Library files `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are unchanged;
their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 211 performed this extraction and namespace adaptation. No patch10 edit
or other worker's implementation draft was used.
