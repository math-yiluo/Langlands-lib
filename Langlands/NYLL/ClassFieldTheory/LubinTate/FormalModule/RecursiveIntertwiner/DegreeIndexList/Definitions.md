# NYLL M353.003: fixed-degree monomial list

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

The source-private `LubinTate.SameUniformizer.degreeIndexList`, lines 51–55,
is published as `Langlands.NYLL.PortInternal.M353.d003`.
For `{sigma : Type w} [Fintype sigma]` and explicit `m : ℕ`, it returns
`List {d : sigma →₀ ℕ // d.degree = m}`. Here `d.degree` is the total degree,
namely the sum of the finitely supported exponents. The body is preserved:
it installs `(Finsupp.finite_of_degree_eq m).fintype` locally on that subtype
and takes `Finset.univ.toList`. The list is obtained by classical choice;
no particular ordering is specified. Nodup and membership are separate targets.

Worker 331 extracted this definition, replaced the source-private name by
the required public port-internal name, and replaced the two original NYLL
imports by `Mathlib.Data.Finsupp.Weight` and `Mathlib.Data.Finset.Dedup`.
These provide the degree finiteness theorem and finite-set-to-list construction
directly. The source's noncomputable section, explicit noncomputable def,
body, docstring, implicit variable type and `Fintype` instance are retained.
Only effective elaborated parameters are included: the source section's
`K`, `Field K`, `F`, and `pi` do not occur in this definition and are not
parameters of it. Its sole universe is the arbitrary variable universe `w`.
Unrelated declarations, unused universes and the original module overview
are omitted; a focused overview and modification notice are added.

Mathlib's `Finsupp`, `Finsupp.degree`, `Finsupp.finite_of_degree_eq`,
`Set.Finite.fintype`, `Finset.univ` and `Finset.toList` are reused.
The source body needs neither `Approximation` nor `linearForm_hasLinearTerm`,
despite the conservative preceding-command edges in the public inventory.
The focused Lean check verifies that these reduced imports suffice.

The original 2026 copyright, Apache-2.0 release and author header are
retained verbatim. Existing `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain unchanged. No patch10 edit affects this source module.
