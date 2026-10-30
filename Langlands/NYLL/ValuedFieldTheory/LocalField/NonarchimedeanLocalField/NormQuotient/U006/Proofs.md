# Concrete evaluation of a norm class

`Langlands.NYLL.LocalFieldTheory.normQuotientConcreteEquiv_normClass.{u}`
proves exactly the published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormQuotientConcreteEquivNormClassStatement.{u}`.
The theorem has no external term parameters and has the sole universe
parameter `u`. The proposition contains all six binders:

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Kˣ),
  Langlands.NYLL.LocalFieldTheory.normQuotientConcreteEquiv K L
      (Langlands.NYLL.LocalFieldTheory.normClass K L x) =
    QuotientGroup.mk x
```

## Implemented proof

The sole direct import is the published U006 `Statements` module. Its
unchanged import chain supplies `normUnits`, `localNormSubgroup`,
`NormQuotient`, `normQuotientCommGroup`, `normQuotientConcreteEquiv`
and `normClass`. The proof first introduces the two fields, their field
structures, the algebra structure and the unit. It then closes the equality
with `rfl`, as in the original source.

This works by definitional equality at Lean's default transparency.
`NormQuotient K L` is the ordinary definition of
`Kˣ ⧸ localNormSubgroup K L`. The published equivalence exposes that
representation and returns `MulEquiv.refl _`, whose underlying function
is the identity. The published `normClass K L` exposes the same quotient
and returns `QuotientGroup.mk' (localNormSubgroup K L)`. Mathlib's
`QuotientGroup.mk'` has underlying function `QuotientGroup.mk`.
Both sides therefore reduce to the same concrete quotient class.
These data definitions are ordinary semireducible definitions, not
reducible abbreviations. No rewriting lemma or new instance is needed.

The subgroup remains the range of
`normUnits K L = Units.map (Algebra.norm K)`. There is no
finite-dimensionality or other additional premise. Mathlib defines this
norm without a finite-module hypothesis; when the algebra is not a
finite module its norm is constantly one, as recorded by
`Algebra.norm_eq_one_of_not_module_finite`. The same representation proof
applies in that case.

This module adds exactly the named theorem, without a simp registration.
It establishes the representation equation only. It supplies no host
adapter, Artin map, norm-kernel, reciprocity, continuity or later M093
construction, and does not complete parent finite reciprocity.

## Source and adaptation

This is the proof phase of M093.006 in
`notes/reuse/nyll-public-port/m073-m096.md`. The original is Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, registered as
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The retained source path is
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`,
SHA-256
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
Original lines 1–100 were read independently: lines 1–5 give attribution,
26–54 the existing data, and 56–63 this theorem and its `rfl` proof.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.normQuotientConcreteEquiv_normClass` | `Langlands.NYLL.LocalFieldTheory.normQuotientConcreteEquiv_normClass` |

Worker 107 added the namespace prefix and changed the theorem's declared
type to the already published closed statement constant. The source's
six external term binders now lie inside that proposition, so the proof
introduces them before the original `rfl`. The shared arbitrary universe
and equation are preserved. The source's unused universe `v`, simp
attribute, source-wide imports, `noncomputable section` and other
declarations are omitted. No computational definition is introduced.
The target's Lean/Markdown pair and all six imported Library dependency
pairs are preserved byte for byte.

Fresh current Library, approved Mathlib and TaskHub searches found no
existing proof of this named equation beyond the current task. Mathlib's
quotient projection is reused through the existing definitions. The
partition lists no patch10 change to this module. Errata locations in
the workspace, project and current Library were checked for both the
source registration above and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`);
no applicable erratum was found.

## Attribution

The original copyright and author header is retained verbatim, including
“Naganori Yamaguchi (assisted by OpenAI Codex)”, with an explicit
modification record. The source is Apache-2.0. The unchanged
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained through
`repository_paths`. Their respective SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
both identical to the originals. The NOTICE has no entry for this
NormQuotient source file. Worker 107 performed this adaptation;
no other project worker's draft was reused.
