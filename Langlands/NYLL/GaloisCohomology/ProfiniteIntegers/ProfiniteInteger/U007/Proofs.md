# NYLL M009.007: reduction of an integer in the profinite integers

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.zHatReduction_intStatement` by the theorem
`Langlands.NYLL.ClassFormation.zHatReduction_int`. The theorem's type is
exactly that proposition applied to its source parameters,
`zHatReduction_intStatement n hn a`.

Its target import is
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U007.Statements`
([`Statements.lean`](Statements.lean)). That published Lean/Markdown pair and
everything it imports are unchanged.

## Target and parameters

The theorem has no universe parameter and the explicit parameters, in the
source order, `n : ℕ` (the modulus), `hn : 0 < n` (needed by
`zHatReduction`) and `a : ℤ`.

The published `zHatReduction_intStatement n hn a` is a reducible alias
(`abbrev`) of the published M008.019 proposition
`zHatReduction_intCastStatement n hn a`, a `def` in
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Statements`.
Unfolding both gives

```lean
zHatReduction n hn (a : ZHat) = (a : ZMod n)
```

Here `ZHat` is the published NYLL closure model of the profinite integers and
`zHatReduction n hn` is its published reduction modulo `n`, the coordinate
at modulus `n`. The theorem says that reducing the image of the integer `a`
in `ZHat` modulo `n` gives the residue class of `a` modulo `n`. The source
writes the left argument as `(Int.castRingHom ZHat) a`. That is
definitionally the cast `(a : ZHat)`, as the statement's Markdown explains.

## Implemented proof

The proof applies the existing M008.019 theorem `zHatReduction_intCast n hn a`, imported from `ProfiniteIntegerCore.U019.Proofs`. The target is a reducible alias of that theorem's proposition, so the required M009.007 API name and complete type are preserved. The [M008.019 proof Markdown](../../ProfiniteIntegerCore/U019/Proofs.md) explains its reflexivity proof by evaluating the closure-model integer cast at modulus `n`.

The `@[simp]` attribute of source line 111 is omitted. The stated type is the
proposition constant `zHatReduction_intStatement n hn a` rather than an
equation, so the attribute would not register the source rewrite rule. The
same choice was made in the published M008.019 proof. The development check
of this module reports no errors or warnings. The theorem has no universe
parameters, and its axioms are only `propext`, `Classical.choice` and
`Quot.sound`. They come from the imported closure-model definitions; the application of the existing theorem adds none.

## Actual dependencies

- The published proposition `zHatReduction_intStatement` and, through its
  body, the published M008.019 proposition `zHatReduction_intCastStatement`.
  Both are used only by definitional unfolding.
- The published M008 definitions `ZHat`, its ring structure and
  `zHatReduction` from
  `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Definitions`,
  reached through the import chain and used only by definitional unfolding.

The published M008.019 theorem `zHatReduction_intCast` is the proof dependency.
No host class-formation, cup, transfer, Tate or reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean:110–116`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean#L110-L116).
Line 110 is the docstring, 111 the `@[simp]` attribute, 112–115 the
signature and 116 the proof `rfl`. The theorem lies in
`namespace ClassFormation` (lines 22–271) and its `noncomputable section`
(lines 26–270). The file has no `variable`, `universe` or `open` command.
The [public partition](../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m009)
lists this theorem as M009.007 (source unit from line 112; the next unit
starts at line 119). The whole-file SHA-256 is
`b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`,
recomputed by Worker 395 on 14 November 2026 UTC from the retained snapshot.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `zHatReduction_int` (M009.007) | Published `zHatReduction_intStatement` in ProfiniteInteger.U007.Statements, an alias of the M008.019 target |
| Proof `zHatReduction_int` | This theorem of the same adapted name in ProfiniteInteger.U007.Proofs |

Worker 395 made these source-extraction changes on 14 November 2026 UTC; integration subsequently reuses M008.019 as described above:

- prefix the namespace with `Langlands.NYLL`;
- replace the source imports (lines 7–11) by the sole published Statements
  import;
- state the theorem's type as the published proposition applied to
  `n hn a`;
- omit the `@[simp]` attribute, as explained above, and all other source
  declarations.

The `noncomputable section`, the docstring, the theorem name, the binders and
their order, and the proof `rfl` are unchanged. They needed no change for the
approved environment.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including "Naganori Yamaguchi
(assisted by OpenAI Codex)", followed by Worker 395's dated modification
record. Worker 395 extracted this proof directly from the pinned original and
the published statement. No unpublished project draft was reused, and there
are no project coauthors. Worker 5454's statement is used unchanged.

The unchanged inherited
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are retained, with SHA-256
values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean `v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Development compilation is
separate from acceptance. Publication under `lean.proof@1` requires the Lake
build, kernel and exact-target checks, unchanged statement and dependency
checks, independent semantic review and Integrator publication.

This proof covers only M009.007. The other ProfiniteInteger units, any host
comparison and any class-formation, cup, transfer, Tate or reciprocity
target are separate work.
