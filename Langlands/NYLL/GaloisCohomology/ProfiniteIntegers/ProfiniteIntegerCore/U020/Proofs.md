# Reduction of one in the profinite integers

This module proves the theorem
`Langlands.NYLL.ClassFormation.zHatReduction_one`.
Its type is the already published proposition
`Langlands.NYLL.ClassFormation.zHatReduction_oneStatement` applied to the
source parameters:

```lean
theorem zHatReduction_one (n : ℕ) (hn : 0 < n) :
    zHatReduction_oneStatement n hn
```

This is the proof phase of M008.020 in the
[NYLL partition](../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m008).

## Target and binders

By its definition in the published `ProfiniteIntegerCore.Statements` module,
`zHatReduction_oneStatement n hn` is the equation

```lean
zHatReduction n hn (1 : ZHat) = 1
```

in `ZMod n`. The binders are exactly the source's, in source order:

| Binder | Kind | Meaning |
| --- | --- | --- |
| `n : ℕ` | explicit | The modulus |
| `hn : 0 < n` | explicit | Its positivity, which selects the coordinate of the closure model |

The left side is the published continuous additive homomorphism
`zHatReduction n hn : ContinuousAddMonoidHom ZHat (ZMod n)` applied to the ring
element one of `ZHat`. The right side is the residue class one in `ZMod n`.
The equation is asserted for every positive modulus `n`, including `n = 1`.
No universe parameter is present and no hypothesis is added.

`ZHat : Type 0` is the published closure model from
`ProfiniteIntegerCore.Definitions`: the topological closure `d007` of the
subring `d006`, the range of the diagonal ring map `d005 : ℤ →+* d004` into
the product `d004 = ∀ i : d001, ZMod i.modulus` over positive moduli. Its ring
structure is the published instance `PortInternal.M008.d009`, inherited from
that closed subring. The reduction `zHatReduction n hn` takes the value of the
underlying family at the index `d003 n hn = ⟨n, hn⟩`.

The sole direct import is the published
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Statements`
module. It imports the published `ProfiniteIntegerCore.Definitions` module,
which supplies `ZHat`, its instances and `zHatReduction`, and the published
`TopologicalGeneration.Definitions` module, which this proof does not use. No
other M008 proof is used; in particular the proof does not import a proof of
M008.019 (`zHatReduction_intCast`), none being in the Library.

## Implemented proof

```lean
unfold zHatReduction_oneStatement
have h : zHatReduction n hn ((1 : ℤ) : ZHat) = ((1 : ℤ) : ZMod n) := rfl
simpa only [Int.cast_one] using h
```

1. `unfold zHatReduction_oneStatement` replaces the statement constant by its
   defining equation `zHatReduction n hn (1 : ZHat) = 1`. Without this step,
   `simpa` cannot match its simplified hypothesis against the unexpanded
   constant.
2. The local fact `h` is the source theorem `zHatReduction_intCast n hn 1`
   (M008.019) at the integer one, proved, as in the source, by `rfl`. It holds
   by definitional unfolding: the ring structure of the closure subring
   (`Subring.toCommRing`, which is `SubringClass.toCommRing`) takes its
   integer cast from `SubringClass.toHasIntCast`
   (`Mathlib/Algebra/Ring/Subring/Defs.lean`, lines 96–97), the ambient
   integer cast paired with its membership proof; the integer cast into the
   product `d004` is coordinatewise;
   `zHatReduction n hn` reads the coordinate at `d003 n hn`, and the modulus
   of `d003 n hn` reduces to `n`. Hence both sides are the integer cast of
   `1 : ℤ` into `ZMod n`.
3. `simpa only [Int.cast_one] using h` rewrites both sides of `h` with
   `Int.cast_one : ((1 : ℤ) : R) = 1` (`Mathlib/Data/Int/Cast/Basic.lean`,
   line 80), for `R = ZHat` on the left and `R = ZMod n` on the right. The
   simplified fact is `zHatReduction n hn 1 = 1`, which closes the goal.

The development check reports that the theorem uses only `propext`,
`Classical.choice` and `Quot.sound`, all already used by the imported
definitions and Mathlib; the proof adds no further axiom.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean`,
lines 132–135](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean#L132-L135):
the docstring at 132, the `@[simp]` theorem and its signature at 133–134 and
the proof `simpa only [Int.cast_one] using zHatReduction_intCast n hn 1` at
135. Its prerequisite `zHatReduction_intCast`, with proof `rfl`, is at lines
125–130. Both lie in the `ClassFormation` namespace at lines 22–226, whose
`open scoped Topology` directive at line 26 is not needed here. The complete
original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean`;
it was read and its SHA-256 verified as
`a6cdc6d3cfca209257868daa4e1aa09ca4f83d08927114958d2737b93b309ae5`.

| Original declaration | Adapted declaration in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| `ClassFormation.zHatReduction_one` (theorem) | `zHatReduction_one` (theorem), proving the published target at `n hn` |
| Same theorem's statement | Existing `zHatReduction_oneStatement` |
| `ClassFormation.zHatReduction_intCast` at `a = 1` | Local fact `h` inside the proof; no declaration |
| `ClassFormation.zHatReduction`, `ClassFormation.ZHat` | Existing `zHatReduction`, `ZHat` |

Only the first row introduces a declaration here. Modifications by
Worker 120 on 13 November 2026 are:

- add the `Langlands.NYLL` namespace prefix and replace the source imports
  with the sole Statements import;
- give the theorem the published statement applied to `n hn` as its type and
  unfold it at the start of the proof;
- replace the call `zHatReduction_intCast n hn 1` by the local fact `h`,
  proved by the same `rfl` as the source's `zHatReduction_intCast`, because no
  proof of M008.019 is in the Library;
- omit the `@[simp]` attribute. The theorem's type is the statement constant,
  not a syntactic equation, so it would not give the source simp lemma.
  The rewrite is available from the published statement after unfolding;
- reword the docstring. The source docstring speaks of reduction modulo one,
  while the source signature asserts that one is sent to one at every positive
  modulus. The adapted docstring describes the signature, as the published
  statement's Markdown already records.

The theorem name, binder names, binder order and the `Int.cast_one`
simplification step are kept. The partition records no patch10 change to this
original module.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL or profinite-integer erratum was found in the Library errata notes.
Searches of staging and shared drafts for `zHatReduction_one` found no earlier
proof port of this theorem.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. A
development check compiled the module with no diagnostics and found a theorem
with no level parameters, using only the three axioms above. This check does
not establish independent semantic acceptance or Integrator publication.

## Attribution and boundary

The original copyright and author header is preserved verbatim:
copyright 2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted
by OpenAI Codex)”, released under Apache-2.0. The Lean file carries the
dated modification record. Worker 120 adapted this proof directly from
the pinned original and wrote this companion. No other project worker
supplied code or a reused draft for this proof. The published
`ProfiniteIntegerCore.Definitions` and `ProfiniteIntegerCore.Statements`
modules, all other imported Library modules and their paired Markdown are
used unchanged.

The unchanged [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are included in
`repository_paths` and are byte-identical to the retained originals.
Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No Mathlib code is copied into this file.

This computation proves only M008.020. It does not prove M008.019 as a
declaration, nor any other M008 theorem. It asserts no comparison with
another model of the profinite integers and no reciprocity result.
