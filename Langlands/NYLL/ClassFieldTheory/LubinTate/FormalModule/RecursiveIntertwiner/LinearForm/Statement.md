# NYLL M353.001: linear form has the prescribed linear term

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

The source theorem `LubinTate.SameUniformizer.linearForm_hasLinearTerm`
has statement at lines 41–43 and proof at line 44. Its exact proposition is
published here as the Prop-valued definition
`Langlands.NYLL.LubinTate.SameUniformizer.linearForm_hasLinearTermStatement`:
for explicit `L : sigma → F.valuationSubring`, the proposition is
`HasLinearTerm (linearForm L) L`.

Its implicit parameters remain `{K : Type u} [Field K]`,
`{F : LocalField.{u, v} K}`, and `{sigma : Type w} [Fintype sigma]`.
The field, value-group and variable universes are independent. The unused
section variable `pi` is absent, as in the elaborated source theorem; there
is no uniformizer hypothesis and no Lubin–Tate series parameter. The local-field
scope is retained even though the published linear-term definitions are more
general. `LocalField` is the shared adapted package extending `CompleteDVF`
and supplying a finite residue field.

Worker 331 extracted the proposition, prefixed the source namespace and
opened namespace by `Langlands.NYLL`, replaced the theorem/proof by a `def`
with the `Statement` suffix, and retained its docstring and effective binders.
The body is precisely the original theorem's conclusion. The original two
NYLL imports are replaced by the focused published LocalField and LinearTerm
Definitions modules; the unused section variable, unrelated declarations
and original overview are omitted. A focused overview and modification
notice are added. The focused Lean check verifies this reduced import set.
The source's noncomputable section and three universes are retained.

The existing `linearForm`, `HasLinearTerm` and valuation-subring constructions
are reused by Lean name. This pair contains a target only. Its exact theorem
`Langlands.NYLL.LubinTate.SameUniformizer.linearForm_hasLinearTerm` must be
published by a separate proof task after this target is integrated; that proof
is required before the stage-zero approximation in M353.016 can be constructed.

The original 2026 copyright, Apache-2.0 release and author header are
retained verbatim. Existing `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain unchanged. No patch10 edit affects this source module.
