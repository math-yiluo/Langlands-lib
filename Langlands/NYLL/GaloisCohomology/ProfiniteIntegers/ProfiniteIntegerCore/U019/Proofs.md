# Reduction of an integer cast in the profinite integers

This module proves the theorem
`Langlands.NYLL.ClassFormation.zHatReduction_intCast`.
Its type is the already published proposition
`Langlands.NYLL.ClassFormation.zHatReduction_intCastStatement`
from [`../Statements.lean`](../Statements.lean), applied to the theorem's
own source parameters:

```lean
theorem zHatReduction_intCast (n : ℕ) (hn : 0 < n) (a : ℤ) :
    zHatReduction_intCastStatement n hn a
```

This is the proof phase of M008.019 in the
[NYLL partition](../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m008).

## Target and binders

The statement unfolds to

```lean
zHatReduction n hn (a : ZHat) = (a : ZMod n)
```

| Binder | Kind | Meaning |
| --- | --- | --- |
| `n : ℕ` | explicit | The modulus |
| `hn : 0 < n` | explicit | Positivity of the modulus, needed by `zHatReduction` |
| `a : ℤ` | explicit | An ordinary integer |

The binders are explicit and in the source order `n`, `hn`, `a`. There is
no universe parameter and no other hypothesis.

`ZHat : Type 0` and `zHatReduction n hn : ContinuousAddMonoidHom ZHat (ZMod n)`
are the published NYLL definitions from
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Definitions`,
imported unchanged through the Statements module. `ZHat` is the closure
`d007` of the subring `d006`, the range of the diagonal ring map
`d005 : ℤ →+* d004`. Here `d004` is the product of `ZMod i.modulus` over
positive-modulus indices `i : d001`, and `d005` sends `a` to
`fun i => (a : ZMod i.modulus)`. The map `zHatReduction n hn` takes the
coordinate of the underlying product element at the index `d003 n hn = ⟨n, hn⟩`.
All `d00k` names are in `Langlands.NYLL.PortInternal.M008`. The left side
casts `a` into `ZHat` with the ring structure `d009`. The right side is
the ordinary integer cast into `ZMod n`. So the theorem says that reducing
the integer `a`, viewed in `ZHat`, modulo `n` gives the residue class of
`a` modulo `n`.

## Implemented proof

The proof is the single term `rfl`, unchanged from the original. Both sides
agree by definitional unfolding, which Lean's kernel checks:

1. `zHatReduction_intCastStatement n hn a` is a `def` and unfolds to the
   displayed equation.
2. The `IntCast ZHat` instance comes from `d009 : CommRing ZHat`, which is
   the instance found on `d007` after `change CommRing d007`. A development
   `#synth` check identified it as Mathlib's `Subring.toCommRing` for the
   closure subring, over `Pi.commRing` on `d004`. `Subring.toCommRing`
   (`Mathlib/Algebra/Ring/Subring/Defs.lean`, lines 362–363) is
   `SubringClass.toCommRing` (same file, lines 122–126). Its integer cast
   is `SubringClass.toHasIntCast` (same file, lines 96–97). It sends `a`
   to the subtype element whose value is the ambient cast `(a : d004)`.
3. `Pi.commRing` takes its integer cast from `Pi.addGroupWithOne`
   (`Mathlib/Algebra/Ring/Pi.lean`, lines 47–52), with field
   `intCast n _ := n`. So `(a : d004)` is the function `fun i => (a : ZMod i.modulus)`.
4. `zHatReduction n hn` evaluates the value of its argument at
   `d003 n hn = ⟨n, hn⟩`, whose `modulus` field reduces to `n`. The result is
   `(a : ZMod n)`, the right-hand side.

The proof uses only the definitions above. No closure, density, continuity
or extensionality fact is used. All cited Mathlib locations are in the
approved environment's Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The proof uses no other M008 theorem and no Library result other than the
imported published definitions and statement.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean`,
lines 125–130](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean#L125-L130).
The docstring is at lines 125–127, the `@[simp]` theorem with its binders and
conclusion at 128–129, and the proof `rfl` at 130. It lies in
`namespace ClassFormation` (lines 22–226), which opens `Topology` as a
scoped namespace at line 26. The complete original file (226 lines) was read,
and its SHA-256 was verified as
`a6cdc6d3cfca209257868daa4e1aa09ca4f83d08927114958d2737b93b309ae5`.
A retained copy is at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean`.

| Original declaration | Adapted declaration in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| `ClassFormation.zHatReduction_intCast` (theorem) | `zHatReduction_intCast` (theorem), proving the published target |
| Same theorem's statement | Existing `zHatReduction_intCastStatement` |
| `ClassFormation.zHatReduction`, `ClassFormation.ZHat` | Existing `zHatReduction`, `ZHat` |
| Private `zHatIndex`, `ZHatAmbient`, `zHatDiagonal`, `zHatIntegerSubring`, `ZHatClosureModel` | Existing `PortInternal.M008.d003`, `d004`, `d005`, `d006`, `d007` |

Only the first row introduces a declaration here. Worker 124 made these
changes on 13 November 2026:

- add the `Langlands.NYLL` namespace prefix;
- replace the source imports with the single import
  `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Statements`;
- state the conclusion as `zHatReduction_intCastStatement n hn a`, which
  unfolds definitionally to the original conclusion;
- omit the `@[simp]` attribute, because the stated type is the unexpanded
  proposition constant rather than an equation;
- omit the unused `open scoped Topology` directive and all other source
  declarations.

The original theorem name, binders and their order, the docstring and
the proof `rfl` are kept. The partition records no patch10 change to this
original module.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The current Library errata notes have no NYLL or ProfiniteIntegerCore
erratum. Searches of the current Library, staging and shared drafts found
no earlier proof port of this theorem, so no draft was reused.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`, with
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean `v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The original `rfl` proof needed
no change for the approved environment. A development check compiled the
module with no errors or warnings. It found a theorem with no universe
parameters, and its axioms are only `propext`, `Classical.choice` and
`Quot.sound`. These come from the imported closure-model definitions;
the `rfl` term itself adds none. This check does not establish independent
semantic acceptance or Integrator publication.

## Attribution and boundary

The original copyright and author header is preserved verbatim:
copyright 2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted
by OpenAI Codex)”, released under Apache-2.0. The Lean file carries the
dated modification record. Worker 124 adapted this proof directly from
the pinned original and wrote this companion. No other project worker
supplied code or a reused draft for this proof. Worker 120's definitions
and statement are used unchanged. All imported Library modules and their
paired Markdown remain frozen.

The unchanged [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are included in
`repository_paths` and are byte-identical to the retained originals.
Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The original NOTICE does not list this source module. No Mathlib code is
copied into this file.

This proof establishes only M008.019. It does not prove M008.020–024, and
it gives no host-model comparison and no class-formation or reciprocity
result.
