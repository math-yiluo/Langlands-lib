# Integral-representation group universe

`Langlands.NYLL.IntegralRepGroupType` is an abbreviation for `Type 0`.
It names the source's universe-zero group boundary for integral representations.
This is a type-valued alias, with no parameters or instances, rather than a
mathematical assertion or a representation construction.

The complete declaration is:

```lean
abbrev Langlands.NYLL.IntegralRepGroupType := Type 0
```

The alias has type `Type 1`. It preserves the fixed universe of the source;
it does not generalize integral representation theory to arbitrary groups.

## Source correspondence

| Source unit and original name | Adapted name |
| --- | --- |
| M002.001, `IntegralRepGroupType`, line 18 | `Langlands.NYLL.IntegralRepGroupType` |

The exact source is `Nyll/GaloisCohomology/Cyclic/IntegralRepUniverse.lean`,
lines 8–18, whose SHA-256 is
`0d58cfdb9f43f739612614d3c9ccde19861ae76dfdf3c9c1ee3ebfc773aef00c`.
The source is Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, retained under
`literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The registered original is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was found in the available project notes.

The source contains no imports. The abbreviation body is unchanged; this
extraction adds only the `Langlands.NYLL` namespace and a modification notice,
and replaces the module prose with this focused description. There are no
new global instances, laws, helper results or other source declarations.
The Lean-service check compiled this module without imports.

## Attribution

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi; authors Naganori Yamaguchi (assisted by OpenAI Codex).
The unchanged Apache-2.0 [LICENSE](../../../../licenses/NYLL/LICENSE) and [NOTICE](../../../../licenses/NYLL/NOTICE) accompany this
subset at `licenses/NYLL/`. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
These bytes were verified against the carried-license manifest. The original
NOTICE has no source-specific entry for this extracted file. Worker 120 made
the recorded extraction and namespace/import changes on 9 November 2026;
no earlier adaptation or patch10 code is incorporated.
