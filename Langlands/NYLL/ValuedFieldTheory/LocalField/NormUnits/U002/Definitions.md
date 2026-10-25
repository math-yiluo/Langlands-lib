# General field norm on unit groups

`Langlands.NYLL.LocalFieldTheory.normUnits` is the restriction of Mathlib's
algebra norm to unit groups. Its complete telescope is

```lean
(K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] : Lˣ →* Kˣ
```

The universes `u` and `v` are independent. The noncomputable definition is
exactly `Units.map (Algebra.norm K)`. It requires no finite-dimensionality,
valuation, topology, local-field, separability or Galois assumption. Mathlib's
`Algebra.norm` is a monoid homomorphism defined by the determinant of
multiplication; `Units.map` applies that homomorphism to the value and inverse
of each unit. This uses Mathlib's general norm convention, including its value
one when the algebra is not a finite module.

## Source and correspondence

This is unit M092.002 of the NYLL declaration partition. The exact original is
Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean`: lines 21–24 give the
universe and field-algebra parameters, and lines 33–34 define `normUnits`.
The original file's SHA-256 is
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.
The complete original file was read for this extraction.

The source is retained under the registered snapshot
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
in its `n-yamaguchi-0729--ClassFieldTheory/source/` directory. The attribution
supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was found in the project's published errata lookup.
The accepted compatibility inventory records no patch10 change to this source
module.

| Original name | Adapted name |
| --- | --- |
| `LocalFieldTheory.normUnits` | `Langlands.NYLL.LocalFieldTheory.normUnits` |

The source telescope, result type and body are unchanged. The unused source
universe `w` belongs to the later tower theorem and is omitted here.

## Imports, reuse and scope

The sole import is `Mathlib.RingTheory.Norm.Transitivity`, also the original
module's sole import. No NYLL declaration is needed by the definition body.
A focused Lean-service build and complete declaration inspection succeeded
in Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, without diagnostics, retaining
independent `u` and `v`. This verifies the Mathlib-only closure for this unit.
The partition's textual predecessor M092.001.END refers to `algebraNorm_neg`;
that theorem is neither imported nor copied. This unit contains just the
single definition. The source's later evaluation and tower theorems are
excluded and require separate statement and proof units.

The existing host definition `Langlands.LocalClassField.normUnits` in
`Langlands/ClassFieldTheory/Local/Norms.lean` has the additional explicit
instance parameter `[FiniteDimensional K L]`. Under that finite specialization,
both definitions unfold to the same expression `Units.map (Algebra.norm K)`.
The host module is unchanged and is not imported here; this observation is
not submitted as a separate comparison theorem.

This definition supplies algebraic data for later norm subgroups and quotients.
It constructs no Artin map and proves no reciprocity statement.

## Attribution and modifications

The original copyright and author header is retained verbatim: copyright 2026
Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`), all rights reserved;
authors Naganori Yamaguchi (assisted by OpenAI Codex). The source is released
under Apache-2.0. The unchanged upstream
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are already in the Library
and remain included through the submission's repository paths. Their SHA-256
hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The upstream NOTICE contains no source-specific entry for `NormUnits.lean`.

Worker 107 extracted the single source definition on 25 October 2026,
added the `Langlands.NYLL` namespace prefix, omitted the unused universe and
all other source declarations, and wrote this documentation. The definition
body and original Mathlib import are unchanged. No patch10 code or other
worker's draft was reused.
