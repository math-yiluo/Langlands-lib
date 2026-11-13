# Finite-quotient subgroups of the NYLL profinite integers

This module proves the theorem
`Langlands.NYLL.ClassFormation.zHatAddSubgroup_eq_mulNat_range_of_finite_quotient`.
Its type is the already published proposition
`Langlands.NYLL.ClassFormation.zHatAddSubgroup_eq_mulNat_range_of_finite_quotientStatement H`
from [`../Statements.lean`](../Statements.lean), applied to the theorem's own
source parameters. This is the proof phase of M009.014 in the
[NYLL partition](../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m009).

## Theorem and binders

```lean
theorem zHatAddSubgroup_eq_mulNat_range_of_finite_quotient
    (H : AddSubgroup ZHat) [Finite (ZHat ⧸ H)] :
    zHatAddSubgroup_eq_mulNat_range_of_finite_quotientStatement H
```

| Binder | Kind | Meaning |
| --- | --- | --- |
| `H : AddSubgroup ZHat` | explicit | An arbitrary additive subgroup of the profinite integers |
| `[Finite (ZHat ⧸ H)]` | instance-implicit | The quotient coset type `ZHat ⧸ H` is finite |

These are the source binders in the source order. There is no closedness
or openness premise on `H` and no hypothesis on its index. The target
unfolds to `H = (zHatMulNat H.index).toAddMonoidHom.range`: `H` is the
image of multiplication by its own natural index `H.index`. Here `ZHat` is
the published `Type 0` closure model (the closure of the diagonal image of
`ℤ` in `∀ i, ZMod i.modulus` over all positive moduli), with its published
ring structure, subspace topology and compactness instance. `zHatMulNat n`
is the published continuous additive map `x ↦ n • x`, and `zHatReduction n
hn` is the published reduction to `ZMod n`. All are imported unchanged
through the Statements module. The theorem has no universe parameters.

## Implemented proof

The theorem (Lean lines 178–184) applies the helper
`PortInternal.M009U014.zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero` to
`H` and Mathlib's `AddSubgroup.index_ne_zero_of_finite`
(`Mathlib/GroupTheory/Index.lean`, line 533), which turns the instance
`[Finite (ZHat ⧸ H)]` into `H.index ≠ 0`. This is the source proof of
M009.014 (source lines 228–229). The published target is a definition that
unfolds definitionally to the helper's conclusion, so the term is accepted
without an explicit unfolding step.

The source proves this by citing M009.012, which depends on M009.011, M009.010
and further lemmas. None of these, nor the core density lemma M008.023,
have a published proof in the current Library, and Tasks 5766 and 5767,
which own the exact M009.011 and M009.012 proofs, have not published one.
This module therefore ports the needed source proofs as seven helper
theorems in the namespace `Langlands.NYLL.PortInternal.M009U014` (Lean lines
33–174). They live in a module-specific internal namespace so that they
cannot clash with the exact public theorems that the other M009 tasks will
publish under `Langlands.NYLL.ClassFormation`. They have the source
statements, except that names of private source declarations are replaced
by their published names (see the table below).

1. `denseRange_intCast_zHat : DenseRange (Int.castRingHom ZHat)` (Lean
   lines 39–67; port of M008.023). The inclusion of the integer subring
   `d006` into its topological closure has dense range by
   `denseRange_inclusion_iff` (`Mathlib/Topology/Constructions.lean`, line
   497). The corestriction `d005.rangeRestrict` of the diagonal map `ℤ → ∀ i,
   ZMod i.modulus` is surjective, so it has dense range. Their composite
   has dense range, and it equals `Int.castRingHom ZHat` pointwise by `rfl`
   after `Subtype.ext` and `funext`.
2. `isClosed_zHatMulNat_range n` (Lean lines 69–73; port of M009.006). The
   range of the continuous map `zHatMulNat n` on the compact space `ZHat` is
   compact, hence closed in the Hausdorff space `ZHat`.
3. `zHatReduction_surjective n hn` (Lean lines 75–81; port of M009.008).
   Every residue is the cast of an integer `a` (`ZMod.intCast_surjective`),
   and the reduction of `Int.castRingHom ZHat a` is `(a : ZMod n)` by `rfl`.
4. `zHatMulNat_int n a` (Lean lines 83–93; port of M009.009). It states
   `zHatMulNat n (Int.castRingHom ZHat a) = Int.castRingHom ZHat (n * a)`.
   The proof changes the left side to `n • Int.castRingHom ZHat a` and
   rewrites with `map_mul`, `map_natCast` and `nsmul_eq_mul`.
5. `zHatMulNat_range_eq_ker_reduction n hn` (Lean lines 95–129; port of
   M009.010). The range `n ZHat` equals the kernel `K` of `zHatReduction n
   hn`. One inclusion holds because reduction is additive, so `n • x` maps
   to `n • zHatReduction n hn x`, which is zero in `ZMod n` because
   `(n : ZMod n) = 0`. For the other, `K` is open, being the
   preimage of `{0}` in the discrete space `ZMod n`, and the integers `D`
   are dense by step 1. So every point of `K` lies in `closure (K ∩ D)`
   (`Dense.open_subset_closure_inter`, `Mathlib/Topology/Neighborhoods.lean`,
   line 318). An integer `a` in `K` has `(a : ZMod n) = 0`, so `n ∣ a` by
   `ZMod.intCast_zmod_eq_zero_iff_dvd` (`Mathlib/Data/ZMod/Basic.lean`, line
   513). Writing `a = n * b`, step 4 puts it in `n ZHat`. Since `n ZHat` is
   closed (step 2), `closure_minimal` (`Mathlib/Topology/Closure.lean`, line
   199) gives `K ⊆ n ZHat`.
6. `zHatMulNat_range_index n hn` (Lean lines 131–147; port of M009.011).
   `(n ZHat).index = n`. By step 5 and `AddSubgroup.index_ker`
   (`Mathlib/GroupTheory/Index.lean`, line 282), the index is the cardinality
   of the range of reduction. That range is `⊤` by step 3, and
   `Nat.card (⊤ : AddSubgroup (ZMod n)) = Nat.card (ZMod n) = n` by an
   explicit equivalence and `Nat.card_zmod`.
7. `zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero H hH` (Lean lines
   149–170; port of M009.012). Let `n = H.index ≠ 0`. Then `n ZHat ≤ H`,
   since `n • x ∈ H` for every `x` by `AddSubgroup.nsmul_index_mem` (the
   additive form of `Subgroup.pow_index_mem`,
   `Mathlib/GroupTheory/OrderOfElement.lean`, lines 1226–1228; `H` is
   normal in the commutative group). By `AddSubgroup.relIndex_mul_index`
   (`Mathlib/GroupTheory/Index.lean`, line 107) and step 6,
   `(n ZHat).relIndex H * n = n`. Cancelling `n > 0` gives relative index
   `1`. So `H ≤ n ZHat` by `AddSubgroup.relIndex_eq_one` (same file, line
   474), and `le_antisymm` concludes.

Closedness of `H` is never assumed. The topology enters only in steps 1, 2
and 5, through the published subspace topology, compactness and the
continuity of the published maps. The finite index alone then forces `H` to
be the closed subgroup `n ZHat`. All cited Mathlib locations are in the
approved environment's Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

## Imports

The only import is
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements`,
which brings the published M009 targets, the multiplication map module
`…ProfiniteInteger.U002.Definitions`, the closure-model module
`…ProfiniteIntegerCore.Definitions` and Mathlib's `Mathlib.GroupTheory.Index`.
The helpers use the published internal names `PortInternal.M008.d004`,
`d005` and `d006` of the closure model. No other Library module and no new
definition, instance or axiom is introduced. The development check reports
exactly the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The target passage is
[`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`, lines
223–229](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean#L223-L229):
the docstring at 223–224, the signature at 225–227 and the proof at
228–229. It lies in the source `noncomputable section` (lines 26–270) of
namespace `ClassFormation`. The complete file was read and its SHA-256
verified as
`b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`. The
ported helper proofs come from lines 104–212 of the same file and from
`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean`, lines
169–196, whose SHA-256 was verified as
`a6cdc6d3cfca209257868daa4e1aa09ca4f83d08927114958d2737b93b309ae5`.
Retained copies are under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/ProfiniteIntegers/`.

| Original declaration (source lines) | Declaration here | Partition unit |
| --- | --- | --- |
| `ClassFormation.zHatAddSubgroup_eq_mulNat_range_of_finite_quotient` (223–229) | `Langlands.NYLL.ClassFormation.zHatAddSubgroup_eq_mulNat_range_of_finite_quotient`, typed by the existing published statement | M009.014 |
| `ClassFormation.denseRange_intCast_zHat` (core 169–196) | `PortInternal.M009U014.denseRange_intCast_zHat` | M008.023 |
| `ClassFormation.isClosed_zHatMulNat_range` (104–108) | `PortInternal.M009U014.isClosed_zHatMulNat_range` | M009.006 |
| `ClassFormation.zHatReduction_surjective` (118–123) | `PortInternal.M009U014.zHatReduction_surjective` | M009.008 |
| `ClassFormation.zHatMulNat_int` (125–136) | `PortInternal.M009U014.zHatMulNat_int` | M009.009 |
| `ClassFormation.zHatMulNat_range_eq_ker_reduction` (138–172) | `PortInternal.M009U014.zHatMulNat_range_eq_ker_reduction` | M009.010 |
| `ClassFormation.zHatMulNat_range_index` (174–189) | `PortInternal.M009U014.zHatMulNat_range_index` | M009.011 |
| `ClassFormation.zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero` (191–212) | `PortInternal.M009U014.zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero` | M009.012 |
| private `zHatIntegerSubring`, `zHatDiagonal`, `ZHatAmbient` (core) | existing `PortInternal.M008.d006`, `d005`, `d004` | M008 |
| `ClassFormation.ZHat`, `zHatReduction`, `zHatMulNat` | existing published definitions, unchanged | M008, M009.002 |

The modifications by Worker 111 on 13 November 2026 are:

- add the `Langlands.NYLL` namespace prefix. Put the seven helpers in
  `Langlands.NYLL.PortInternal.M009U014` and the target theorem in
  `Langlands.NYLL.ClassFormation`;
- replace the source imports by the sole import of the published
  ProfiniteInteger Statements module;
- give the target theorem the published proposition applied to `H` as its
  type. Its proof applies the local M009.012 helper instead of the source's
  public theorem;
- in the density helper, replace the private source names
  `zHatIntegerSubring`, `zHatDiagonal` and `ZHatAmbient` by their published
  names `d006`, `d005` and `d004`; the proof steps are otherwise unchanged;
- prove the M009.009 helper by `change n • _ = _` and rewriting with
  `map_mul`, `map_natCast` and `nsmul_eq_mul`. This replaces the source's
  `ZHat.ext`-based proof, since `ZHat.ext` (M008) has no published proof.
  The source `@[simp]` attribute is omitted;
- in the M009.010 helper, prove `ha0 : (a : ZMod n) = 0` directly as the
  kernel membership `hzK`, which is definitionally that equation. The source
  `simpa [K] using hzK` relied on the source simp lemma `zHatReduction_int`
  (M009.007), which is not ported;
- append a port remark to each helper docstring, and omit all other source
  declarations, including M009.007, M009.013 and the source simp
  attributes.

The M008.023, M009.006, M009.008, M009.011 and M009.012 proof steps,
and all M009.010 steps other than `ha0`, are the source steps. The source
theorem name and docstring of the target are kept.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. Additional attribution
material is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Searches of the current Library, staging and shared drafts found no
earlier proof port of this theorem or of the M009.011 and M009.012
prerequisites, so no draft was reused.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`, with
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. A
development check compiled the module with Lake, with no errors or warnings.
It found a theorem with no universe parameters and only the axioms
`propext`, `Classical.choice` and `Quot.sound`. This check does not
establish independent semantic acceptance or Integrator publication.

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright
2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI
Codex)”, released under Apache-2.0. The Lean file carries the dated
modification record. Worker 111 adapted these proofs from the pinned
original and wrote this companion. No other project worker supplied code or
a reused draft. Worker 120's published statements and definitions are used
unchanged. All imported Library modules and their paired Markdown remain
frozen.

The unchanged [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are included in
`repository_paths` and are byte-identical to the Library copies. Their
SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. No
Mathlib code is copied into this file.

This proof establishes only M009.014. The seven internal helpers are not
proofs of the published M008.023 or M009.006–M009.012 targets. Those tasks
still need their exact public theorems, although they may reuse these
proof steps. No host class-formation, cup, Tate, transfer or reciprocity
result is asserted.
