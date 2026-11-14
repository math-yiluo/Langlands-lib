# NYLL M353.004–005: fixed-degree list targets

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

This pair records the exact propositions of two source-private theorems.

| Unit | Original name and complete lines | Prop-valued target |
| --- | --- | --- |
| M353.004 | `LubinTate.SameUniformizer.degreeIndexList_nodup`, 57–60 (statement 57–58) | `Langlands.NYLL.PortInternal.M353.d004Statement` |
| M353.005 | `LubinTate.SameUniformizer.mem_degreeIndexList`, 62–66 (statement 62–64) | `Langlands.NYLL.PortInternal.M353.d005Statement` |

For arbitrary `{sigma : Type w} [Fintype sigma]`, the explicit degree
`m : ℕ` indexes `d003`, the exact list constructed from the finite subtype
of exponent vectors of total degree `m`. `d004Statement m` says that this
list is `Nodup`. For an explicit subtype element
`d : {d : sigma →₀ ℕ // d.degree = m}`, `d005Statement m d` says that `d`
belongs to the list. Both conclusions use the same `d003`; no different
ordering or enumeration is substituted. These targets retain the source's
`Fintype sigma` instance and its sole effective universe. They introduce no
local-field, coefficient-ring, uniformizer or Lubin–Tate-series parameters;
the corresponding source section variables do not enter the elaborated types.

Worker 331 replaced the private theorem names by the specified public
port-internal names with `Statement` suffixes and changed the theorem/proof
commands into Prop-valued definitions of their exact conclusions. Added
docstrings describe these conclusions. The degree list is reused from the
focused Definitions module; the original NYLL imports, unused section
variables and universes, unrelated declarations and original overview are
omitted. The noncomputable section is retained and a focused overview and
modification notice are added. No source proof is included here. Each exact
proof, `Langlands.NYLL.PortInternal.M353.d004` and
`Langlands.NYLL.PortInternal.M353.d005`, requires a separate proof successor
after target publication. The focused Lean check verifies the reduced import
and these exact Prop-valued declarations.

The original 2026 copyright, Apache-2.0 release and author header are
retained verbatim. Existing `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain unchanged. No patch10 edit affects this source module.
