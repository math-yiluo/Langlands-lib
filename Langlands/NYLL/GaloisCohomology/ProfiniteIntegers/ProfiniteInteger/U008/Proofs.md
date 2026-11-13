# Surjectivity of reduction modulo a positive integer

This module proves the theorem
`Langlands.NYLL.ClassFormation.zHatReduction_surjective`.
Its type is the already published proposition
`Langlands.NYLL.ClassFormation.zHatReduction_surjectiveStatement`
applied to the theorem's own parameters:

```lean
theorem zHatReduction_surjective (n : ℕ) (hn : 0 < n) :
    zHatReduction_surjectiveStatement n hn
```

This is the proof phase of M009.008 in the
[NYLL partition](../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m009).

## Target and parameters

The statement unfolds to

```lean
Function.Surjective (zHatReduction n hn)
```

The theorem keeps the source's two explicit parameters in the source order:
first `n : ℕ`, then `hn : 0 < n`. The proof adds no hypothesis.

The statement module states the target with the actual published data,
which this proof imports unchanged:

- `ZHat : Type 0` is the closure model. It is the topological closure of
  the image of the ring map `ℤ →+* ∀ i, ZMod i.modulus`, where `i` ranges over
  the positive moduli. The map sends `a` to the family of its residues. `ZHat`
  carries the ring structure of this closed subring.
- `zHatReduction n hn : ContinuousAddMonoidHom ZHat (ZMod n)` takes an
  element of the closure to its coordinate at the index `⟨n, hn⟩`.

So the theorem says that every residue class modulo `n` is the reduction of
some element of `ZHat`.

## Implemented proof

The proof uses the original proof steps at source lines 121–123 without
change:

```lean
intro a
rcases ZMod.intCast_surjective a with ⟨a, rfl⟩
exact ⟨(Int.castRingHom ZHat) a, rfl⟩
```

1. `intro a` unfolds the statement definition and `Function.Surjective`.
   It introduces an arbitrary residue `a : ZMod n`, and the goal becomes
   `∃ x, zHatReduction n hn x = a`.
2. Mathlib's `ZMod.intCast_surjective` (`Mathlib/Data/ZMod/Basic.lean`,
   line 229) says that the integer cast `ℤ → ZMod n` is surjective.
   `rcases` gets an integer whose cast is the given residue and substitutes
   it, reusing the name `a`. The goal becomes
   `∃ x, zHatReduction n hn x = (a : ZMod n)` for `a : ℤ`.
3. The witness is the image `(Int.castRingHom ZHat) a` of `a` in `ZHat`. The
   remaining equation
   `zHatReduction n hn ((Int.castRingHom ZHat) a) = (a : ZMod n)`
   holds by `rfl`. In `ZHat`, the integer cast is the integer cast of the
   closed subring. Its underlying element of `∀ i, ZMod i.modulus` is the
   pointwise integer cast. `zHatReduction n hn` evaluates that family at
   `⟨n, hn⟩`, which gives `(a : ZMod n)`. The kernel accepts this definitional
   equality.

The equation in step 3 is the source theorem `zHatReduction_int`
(M009.007, source lines 110–116), which is itself proved by `rfl`. That
theorem is not published in the Library and is not imported. As in the
source, the proof uses the definitional equality inline. It uses no M008
theorem proof and no other M009 proof.

## Imports and checks

The only direct import is the published module
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements`,
as the task requires. That module provides the target, `ZHat`, its
instances and `zHatReduction` through its own imports. It also makes
`ZMod.intCast_surjective` and `Int.castRingHom` available. No imported
Library module or paired Markdown is changed.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`: Lean
4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. The original
proof needed no change in this environment. A development `lean_check` built
the module with no errors or warnings. It found the theorem with no universe
parameters. The theorem uses only the axioms `propext`, `Classical.choice`
and `Quot.sound`. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The passage is
[`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`,
lines 118–123](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean#L118-L123):

- line 118: the docstring;
- lines 119–120: the theorem signature;
- lines 121–123: the proof.

The complete original file was read, and its SHA-256 was checked to be
`b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`.

| Original declaration | Adapted declaration in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| `ClassFormation.zHatReduction_surjective` (theorem) | `zHatReduction_surjective` (theorem), proving the published target |
| Same theorem's statement | Existing `zHatReduction_surjectiveStatement` |
| `ClassFormation.ZHat` | Existing `ZHat` |
| `ClassFormation.zHatReduction` | Existing `zHatReduction` |
| `ClassFormation.zHatReduction_int` (rfl lemma) | Not ported; the same definitional equality is used inline |

Only the first row introduces a declaration here. Worker 110 made these
modifications on 13 November 2026:

- added the `Langlands.NYLL` namespace prefix;
- replaced the source imports with the single Statements import;
- gave the theorem the published proposition, applied to `n` and `hn`, as its
  type;
- omitted the source `noncomputable section` and all other source
  declarations.

The theorem name, its docstring, its parameters and the proof steps are
unchanged.

The retained original belongs to the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. Additional attribution material
is registered as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Searches of the workspace, the current Library, staging and shared drafts
found no earlier port of this proof.

## Attribution and boundary

The original copyright and author header is kept verbatim: copyright 2026
Naganori Yamaguchi, author "Naganori Yamaguchi (assisted by OpenAI Codex)",
released under Apache-2.0. The Lean file carries the dated modification
record. Worker 110 adapted this proof directly from the pinned original and
wrote this companion. No other project worker supplied code or a reused
draft. Worker 120's statement and the imported constructions are used
unchanged.

The unchanged [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are in `repository_paths`
and are byte-identical to the retained originals. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No Mathlib code is copied into this file.

This module proves only the stated surjectivity. It asserts no
range–kernel identity, no index computation, no subgroup classification,
no host comparison, and no class-formation or reciprocity result. The other
M009 targets remain separate, and so does parent Task 5264
(`457f00a2-e3a8-49c5-ac1c-07336dacb1b5`).
