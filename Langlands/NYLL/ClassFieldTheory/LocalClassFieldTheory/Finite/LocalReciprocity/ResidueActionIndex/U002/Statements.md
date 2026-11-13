# The whole Galois group as decomposition group: coercion statement

This module defines one closed proposition in
`Langlands.NYLL.LocalClassFieldTheory`, the statement phase of source row
M244.002:

- `toDecompositionGroupOfEqTop_coeStatement`, for the source theorem
  `toDecompositionGroupOfEqTop_coe`.

It is a `def` returning `Prop` that packages the complete source theorem
signature. It has no proof here. A later proof will prove it under the name
`Langlands.NYLL.LocalClassFieldTheory.toDecompositionGroupOfEqTop_coe`.

## The proposition

```lean
def toDecompositionGroupOfEqTop_coeStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L)
    (hA : decompositionGroup K A = ⊤)
    (sigma : L ≃ₐ[K] L),
    (toDecompositionGroupOfEqTop K A hA sigma : L ≃ₐ[K] L) = sigma
```

The definition has the two universe parameters `u` and `v` of the source,
in that order: `K` is a field in an arbitrary universe `u` and `L` a
`K`-algebra field in an independent arbitrary universe `v`. The other
binders are as follows:

- `A` is a valuation ring of `L` (Mathlib's `ValuationSubring`);
- `hA` says that the decomposition group of `A` over `K` is the whole group.
  Here `decompositionGroup K A` is the published NYLL abbreviation (source
  row M239.001) for Mathlib's `A.decompositionSubgroup K`, the subgroup of
  automorphisms `σ` of `L ≃ₐ[K] L` with `σ • A = A`;
- `sigma` is a `K`-algebra automorphism of `L`.

`toDecompositionGroupOfEqTop K A hA` is the published monoid homomorphism
(source row M244.001) from `L ≃ₐ[K] L` to `decompositionGroup K A` that
views every automorphism as an element of the decomposition group, using
`hA` for membership. The conclusion coerces the image of `sigma` back to
`L ≃ₐ[K] L`, through the coercion of a subgroup to its ambient group, and
says that the result is `sigma`. So the homomorphism does not change the
underlying automorphism.

There is no Galois hypothesis. The source file declares the section
variable `[IsGalois K L]`, and Lean would add it to a theorem whose
signature mentions `K` and `L`. The source removes it for this theorem with
`omit [IsGalois K L] in`. The proposition therefore does not quantify over
it. The published M244.001 definition does not take it either, as its
Markdown explains.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M244.001, `LocalClassFieldTheory.toDecompositionGroupOfEqTop` | `Langlands.NYLL.LocalClassFieldTheory.toDecompositionGroupOfEqTop` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex.U001.Definitions`) |
| M239.001, `RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup` | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup` (module `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions`, imported through the M244.001 module) |

`ValuationSubring`, `AlgEquiv` and the subgroup coercion are Mathlib
declarations.

## Relation to other Library and Mathlib declarations

The whole Library at commit `8c25a060978d5f6a41c1b295e956ce494e3b1325` was
searched for `toDecompositionGroupOfEqTop`. The only published declaration
that mentions it is the M244.001 definition itself, and no published
declaration states this proposition. The related homomorphism
`Langlands.LocalGalois.decompositionHom` (module
`Langlands.Galois.Local.SpectralDefinitions`) is also the identity on
underlying automorphisms, but it maps into the decomposition subgroup of
the spectral valuation ring `Langlands.LocalGalois.extensionIntegers K L`
and has no separate coercion lemma. It is a different declaration.

The equation holds by definition, since `toDecompositionGroupOfEqTop`
sends `sigma` to the pair of `sigma` and a membership proof. The source
proves it by `rfl`. Mathlib has no general lemma about this particular
homomorphism.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean>).
The complete file was read and its SHA-256 verified as
`985bdcfc1cc21860cc65bbb96dc92b1a0ec09dc05eadd6d4f46b4b0a551f4581`.
The `omit [IsGalois K L] in` line is line 52, the M244.002 docstring line
53, and the signature lines 54–58; the proof `rfl` is line 59. The header
occupies lines 1–5, the namespace line 22, the `open` lines 24, 26 and 34,
the `noncomputable section` line 30, the `universe` line 32, the section
variables lines 36–37, and the closing `end` lines 112–113.

| Source unit and original declaration | Adapted declaration and phase |
| --- | --- |
| M244.002, `LocalClassFieldTheory.toDecompositionGroupOfEqTop_coe` | `Langlands.NYLL.LocalClassFieldTheory.toDecompositionGroupOfEqTop_coeStatement`, closed Prop target |
| Same source theorem, later proof phase | `Langlands.NYLL.LocalClassFieldTheory.toDecompositionGroupOfEqTop_coe`, reserved for the proof |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 85 made these changes to the source theorem:

- The theorem becomes a Prop-valued definition with the `Statement`
  suffix. The section variables `K` and `L` and their `Field` and `Algebra`
  binders become the leading universal binders, in source order and with
  the source binder kinds (`K` explicit, `L` implicit). The section
  variable `[IsGalois K L]` is not included, as the source's
  `omit [IsGalois K L] in` directs. The explicit binders `A`, `hA` and
  `sigma` and the conclusion are the source text. The proof is omitted for
  the separate proof phase.
- The `@[simp]` attribute is omitted, since a proposition definition is not
  a simp lemma.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
  The source line `open HilbertRamification.ValuationSubring`, which is
  resolved inside the source's `open RamificationTheory`, becomes
  `open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`,
  so that `decompositionGroup` names the published abbreviation.
- The source imports are replaced by the Library module
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex.U001.Definitions`.
- The `noncomputable section`, the `open RamificationTheory` and
  `open ClassFormation` lines, and all other declarations of the source
  file are omitted. The `universe u v` line is kept.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M244.002 statement target. Its proof and the
other rows of the source file are not part of this unit.
