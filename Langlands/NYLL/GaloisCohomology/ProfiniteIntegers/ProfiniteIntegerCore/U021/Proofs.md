# Extensionality of the profinite integers

This module proves the theorem `Langlands.NYLL.ClassFormation.ZHat.ext`.
Its type is the already published proposition
`Langlands.NYLL.ClassFormation.ZHat.extStatement`, applied to the theorem's
own source parameters. This is the proof phase of M008.021 in the
[NYLL partition](../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m008).

## Target and binders

The theorem is declared, in namespace `Langlands.NYLL.ClassFormation.ZHat`, as

```lean
theorem ext {x y : ZHat}
    (h : ∀ n (hn : 0 < n), zHatReduction n hn x = zHatReduction n hn y) :
    extStatement h
```

Its parameters are the source parameters of `extStatement`, in the same
order and with the same binder kinds:

| Binder | Kind | Meaning |
| --- | --- | --- |
| `x y : ZHat` | implicit | Two profinite integers of the published Type-zero model |
| `h` | explicit | For every natural number `n` and every proof `hn : 0 < n`, the two reductions `zHatReduction n hn x` and `zHatReduction n hn y` in `ZMod n` are equal |

The type `extStatement h` is the published target applied to these
parameters, with `x` and `y` inferred from `h`. By its definition in
`ProfiniteIntegerCore/Statements.lean` (lines 34–38), it is the equation
`x = y` in `ZHat`. The hypothesis quantifies over positive moduli only: the
reduction `zHatReduction n hn` exists only together with a proof
`hn : 0 < n`, and `h` supplies equality for every such pair. No other
hypothesis, universe parameter or instance argument is added.

`ZHat` is the published Type-zero closure model of
`ProfiniteIntegerCore/Definitions.lean`: the definition `ZHat := d007`
unfolds to the topological closure of the subring `d006`. That subring is the
range of the diagonal ring map `d005 : ℤ →+* d004`. Its ambient ring is the
product `d004 = ∀ i : d001, ZMod i.modulus` over the positive-modulus index
structure `d001`, whose fields are `modulus : ℕ` and `positive : 0 < modulus`.
The reduction `zHatReduction n hn` is the continuous additive homomorphism
whose underlying function sends `x` to the coordinate `x.1 (d003 n hn)` of
its ambient value, where `d003 n hn = ⟨n, hn⟩` (Definitions lines 33–34 and
117–126). All of these are used by their published Lean names and unchanged.

The sole direct import is the published module
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Statements`.
It imports the published `ProfiniteIntegerCore.Definitions`, with that
module's four Mathlib imports, and the published
`TopologicalGeneration.Definitions`; the latter is not used by this proof.
No other M008 proof is used.

## Implemented proof

The proof (Lean lines 36–41) is the original five-step tactic proof,
preceded by one `show`:

```lean
show x = y
apply Subtype.ext
funext i
rcases i with ⟨n, hn⟩
exact h n hn
```

1. `show x = y` replaces the goal `extStatement h` by its definitional
   unfolding, the equation of the two profinite integers.
2. `apply Subtype.ext` uses Lean core's `Subtype.ext`
   (`Init/Core.lean`, line 1380 of the Lean 4.34.0 sources), which proves
   equality of two subtype elements from equality of their values. The
   definition `ZHat := d007` and the abbreviation `d007` unfold during
   unification to the closure subtype, so the goal becomes equality of the
   ambient values `x.1 = y.1` in the product `d004`.
3. `funext i` reduces this equality of dependent functions to equality of
   the `i`-th coordinates in `ZMod i.modulus`, for an arbitrary index
   `i : d001`.
4. `rcases i with ⟨n, hn⟩` decomposes the index into its modulus `n` and
   positivity proof `hn : 0 < n`, so the goal concerns the coordinate at
   `⟨n, hn⟩`.
5. `exact h n hn` closes the goal: `h n hn` states
   `zHatReduction n hn x = zHatReduction n hn y`, and by the definitions of
   `zHatReduction` and `d003` each side reduces definitionally to the
   coordinate at `⟨n, hn⟩` of the corresponding ambient value.

The argument is thus that a profinite integer is determined by its ambient
product coordinates, and every coordinate is a positive-modulus reduction.
No topological fact, such as closedness of the subring or density, is used.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean`,
lines 137–149](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean#L137-L149):
the `namespace ZHat` block at lines 137 and 149, the docstring at line 139,
the `@[ext]` attribute at line 140, the signature at lines 141–144 and the
proof at lines 145–148. The surrounding `namespace ClassFormation` spans
lines 22–226 and has `open scoped Topology` at line 26. The complete
original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean`;
it was read and its SHA-256 verified as
`a6cdc6d3cfca209257868daa4e1aa09ca4f83d08927114958d2737b93b309ae5`.

| Original declaration | Adapted declaration in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| `ClassFormation.ZHat.ext` (theorem) | `ZHat.ext` (theorem), proving the published target applied to its parameters |
| Same theorem's statement | Existing `ZHat.extStatement` |
| `ClassFormation.ZHat`, `ClassFormation.zHatReduction` | Existing `ZHat`, `zHatReduction` |
| `ZHatClosureModel`, `ZHatAmbient`, `ZHatIndex`, `zHatIndex` (private) | Existing `PortInternal.M008.d007`, `d004`, `d001`, `d003` |

Only the first row introduces a declaration here. Modifications by
Worker 113 on 13 November 2026 are: add the `Langlands.NYLL` namespace
prefix; replace the source imports with the sole Statements import; state
the conclusion as `extStatement h` instead of `x = y` and insert
`show x = y` as the first tactic to unfold it; omit the `@[ext]` attribute,
the unused `open scoped Topology` directive and all other source
declarations. The `@[ext]` attribute is omitted because the theorem's
declared conclusion is the named target rather than a literal equation, and
the published statement module likewise omits theorem-only attributes. The
original theorem name, its docstring, the binder names, kinds and order and
the five source tactic lines are kept unchanged. The partition records no
patch10 change to this original module.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL or ProfiniteIntegerCore erratum was found in the Library errata
notes. Searches of staging and shared drafts for `extStatement` found no
earlier proof port of this theorem.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. The
original tactic proof needed no change for this environment. A development
check compiled the module with no diagnostics. It found the theorem
`Langlands.NYLL.ClassFormation.ZHat.ext`, with no level parameters, using
only `propext`, `Classical.choice` and `Quot.sound`. These come from the
imported definitions and Mathlib; the proof adds no axiom. This check does
not establish independent semantic acceptance or Integrator publication.

## Attribution and boundary

The original copyright and author header is preserved verbatim:
copyright 2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted
by OpenAI Codex)”, released under Apache-2.0. The Lean file carries the
dated modification record. Worker 113 adapted this proof directly from
the pinned original and wrote this companion. No other project worker
supplied code or a reused draft for this proof. Worker 120's statement and
definitions and all imported Library modules and their paired Markdown are
used unchanged.

The unchanged [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are included in
`repository_paths` and are byte-identical to the retained originals.
Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No Mathlib code is copied into this file.

This extensionality result proves only M008.021. It supplies none of the
other M008 theorems, no comparison with another model of the profinite
integers and no reciprocity result.
