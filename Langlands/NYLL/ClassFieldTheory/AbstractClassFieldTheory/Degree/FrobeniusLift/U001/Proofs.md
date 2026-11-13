# Positive natural representatives modulo finite-index subgroups of `ℤ̂`

This module proves the theorem
`Langlands.NYLL.ClassFormation.exists_positive_nsmul_one_sub_mem_of_index_ne_zero`.
Its type is the published proposition
`Langlands.NYLL.ClassFormation.exists_positive_nsmul_one_sub_mem_of_index_ne_zeroStatement`
applied to the theorem's parameters. This is the proof phase of M012.001 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m012).

## Target and binders

The theorem has the target's explicit binders in the same order:
`H : AddSubgroup ZHat`, `hH : H.index ≠ 0`, `z : ZHat`. Its statement is

```lean
∃ n : ℕ, 0 < n ∧ z - n • (1 : ZHat) ∈ H
```

Here `ZHat` is the published Type-zero closure model of `ℤ̂`: the closure of
the image of `ℤ` in `∏_{m>0} ℤ/mℤ`, with the subspace topology and the
subring structure. In words, every class of `ℤ̂ / H` for a subgroup `H` of
finite index contains a strictly positive natural multiple `n • 1`.
The theorem adds no hypothesis. In particular `H` is not assumed closed or
open. The positivity `0 < n` is strict.

## Implemented proof

Write `m = H.index`, which is positive because `hH : m ≠ 0`.
The key step is the private helper

```lean
m012u001_mem_of_reduction_eq_zero (H : AddSubgroup ZHat) (hm : 0 < H.index)
    (x : ZHat) (hx : zHatReduction H.index hm x = 0) : x ∈ H
```

which says that the kernel of the reduction `ℤ̂ → ℤ/mℤ` is contained in `H`.

### Main theorem

The main proof keeps the source's choice of representative. Let
`r = zHatReduction m hm z` in `ZMod m` and `n = r.val + m`, so `0 < n` by
`Nat.add_pos_right`. By the helper it suffices to show that
`z - n • 1` reduces to `0` modulo `m`. Since `zHatReduction m hm` is an
additive homomorphism (`map_sub`, `map_nsmul`) and
`zHatReduction m hm 1 = 1` holds by `rfl`, the reduction equals
`r - (n : ZMod m)`. Finally `(n : ZMod m) = r` by `Nat.cast_add`,
`ZMod.natCast_zmod_val`, `ZMod.natCast_self` and `add_zero`, so the
difference is `0` (`sub_self`). These steps are the source's lines 41–53
unchanged.

### Private helpers

The source obtains the key step by rewriting `H` with two M009 theorems
(see below), whose proofs are not yet in the Library. This module instead
proves the following four private theorems. Their names start with
`m012u001_`, so they cannot clash with the adapted M008/M009 names, and they
are private to this module.

1. `m012u001_mem_closure_intCast (y : d007)`: every point of the closure
   model lies in the closure of the set of integer casts. The published
   internal names are `d004` (the product `∀ i, ZMod i.modulus`), `d006`
   (the range of the diagonal ring map `d005 : ℤ →+* d004`) and `d007` (the
   subtype of `d006.topologicalClosure`), opened from
   `Langlands.NYLL.PortInternal.M008`. Mathlib's `closure_subtype` turns
   membership in a closure inside the subtype into membership of `y.1` in
   the closure in `d004` of the image under `Subtype.val`. That image is
   exactly the carrier of `d006`: the value of the integer cast `(a : d007)`
   is `d005 a` by definition, checked by `rfl`. The carrier of
   `d006.topologicalClosure` is by definition `closure d006`, so `y.2`
   closes the goal.
2. `m012u001_denseRange_intCast : DenseRange (Int.cast : ℤ → ZHat)`. This is
   item 1 read through the definition `ZHat := d007`. It has the content of
   M008.023 (`denseRange_intCast_zHat`, stated with `Int.castRingHom ZHat`),
   whose proof is not published.
3. `m012u001_reduction_intCast m hm a : zHatReduction m hm (a : ZHat) = (a : ZMod m)`.
   This has the content of M008.019 and M009.007. It is proved by writing
   `(a : ZHat) = a • 1` (`zsmul_one`), then using `map_zsmul`, the `rfl`
   equation `zHatReduction m hm 1 = 1`, and `zsmul_one` again.
4. `m012u001_mem_of_reduction_eq_zero`, the key step. Let
   `U = (zHatReduction m hm)⁻¹' {0}` and `C = Set.range (fun y => m • y)`.
   - `U` is open: it is the preimage of a set in the discrete space `ZMod m`
     (`isOpen_discrete`) under a continuous map (`map_continuous`).
   - `C` is closed: it is the image of the compact space `ℤ̂` (published
     instance) under the continuous map `y ↦ m • y` (`Continuous.nsmul`),
     hence compact (`isCompact_range`). It is therefore closed in the
     Hausdorff space `ℤ̂` (`IsCompact.isClosed`).
   - `C ⊆ H`: `AddSubgroup.nsmul_index_mem` gives `H.index • y ∈ H` for
     every `y`. This uses only that `ℤ̂` is commutative, so `H` is normal.
   - `U ∩ range Int.cast ⊆ C`: if `(a : ZHat) ∈ U`, then `(a : ZMod m) = 0`
     by item 3. So `(m : ℤ) ∣ a` by `ZMod.intCast_zmod_eq_zero_iff_dvd`.
     Writing `a = m * b`, `(a : ZHat) = m • (b : ZHat)`, which is proved by
     `simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]`.
   - For `x ∈ U`, density (item 2) gives `x ∈ U ∩ closure (range Int.cast)`.
     This lies in `closure (U ∩ range Int.cast)` by `IsOpen.inter_closure`.
     By `closure_minimal`, that closure lies in the closed set `C`, and so in
     `H`.

In mathematical terms, the helper proves `ker(ℤ̂ → ℤ/mℤ) ⊆ mℤ̂ ⊆ H`. The
first inclusion uses density of `ℤ` in the open kernel, closedness of
`mℤ̂`, and divisibility in `ℤ`. The second holds because
`m = [ℤ̂ : H]` annihilates `ℤ̂ / H`.

## Development check

A development `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) built the module with Lake with
no diagnostics. The theorem has no universe parameters and uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`. This check is not
independent acceptance.

## Imports and dependencies

The sole import is the published
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.Statements`
module. Through it the module uses the published closure-model definitions in
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Definitions`:
`ZHat`, its ring, topology, Hausdorff and compactness instances, the
internal `PortInternal.M008.d004`, `d006` and `d007`, and `zHatReduction`.
It also uses Mathlib. It uses no unpublished theorem and no other M008,
M009 or M012 proof.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusLift.lean`
(SHA-256 `a0b7ac8afcc55cad383a16e6dfe093e147770a7e8f5d21c3f8843744b57b7061`,
verified). The theorem is at lines 31–53, with its docstring at
lines 29–30. The partition unit M012.001 covers lines 31–57. It lies in
the `noncomputable section` (line 23) of namespace `ClassFormation`
(lines 17–228). The section variables at line 27 do not occur in this
theorem. The complete original is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusLift.lean`.

Source lines 39–40 rewrite the goal `z - n • 1 ∈ H` with
`zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero H hH` (M009.012) and
`zHatMulNat_range_eq_ker_reduction m hm` (M009.010). Both are in
`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`
(SHA-256 `b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`).
Their statements are published, but their proofs are routed to Tasks
5765 and 5767 and are not in the Library. Following the task's instruction,
this module proves locally, under private non-conflicting names, only what
it needs: the inclusion `ker ⊆ H` instead of the equalities.

| Source ingredient | Location | Here |
| --- | --- | --- |
| `ClassFormation.exists_positive_nsmul_one_sub_mem_of_index_ne_zero` (M012.001) | FrobeniusLift.lean 31–53 | `exists_positive_nsmul_one_sub_mem_of_index_ne_zero` (theorem, this module), proving the existing statement `exists_positive_nsmul_one_sub_mem_of_index_ne_zeroStatement` |
| `zHatMulNat_range_eq_ker_reduction`, inclusion `ker ⊆ range` (M009.010) | ProfiniteInteger.lean 149–172 | the same argument inside `m012u001_mem_of_reduction_eq_zero` |
| `isClosed_zHatMulNat_range` (M009.006) | ProfiniteInteger.lean 105–108 | inline closedness of `C`, by the same compact-image argument |
| `zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero`, inclusion `range ≤ H` (M009.012) | ProfiniteInteger.lean 198–200 | `hCH` inside `m012u001_mem_of_reduction_eq_zero`, by the same `nsmul_index_mem` |
| `zHatMulNat_int` (M009.009), `zHatReduction_int` (M009.007) / `zHatReduction_intCast` (M008.019) | ProfiniteInteger.lean 112–136; ProfiniteIntegerCore.lean 128 | `m012u001_reduction_intCast` and the final `simp only` step |
| `denseRange_intCast_zHat` (M008.023) | ProfiniteIntegerCore.lean 170–196 | `m012u001_mem_closure_intCast`, `m012u001_denseRange_intCast` (different proof: `closure_subtype` instead of `denseRange_inclusion_iff`) |

Modifications by Worker 5168 on 13 November 2026:

- add the `Langlands.NYLL` namespace prefix;
- give the theorem the published statement applied to its parameters as its
  type, and open it with `show ∃ n : ℕ, 0 < n ∧ z - n • (1 : ZHat) ∈ H`;
- replace the rewrite at source lines 39–40 by
  `apply m012u001_mem_of_reduction_eq_zero H hm` followed by the source's
  `change` at line 41;
- add the four private helpers described above;
- replace the source import with the sole Statements import, use
  `open PortInternal.M008` for the published internal closure-model names, and
  omit the unused `open CyclicCohomology`, the section variables and all other
  source declarations.

The original theorem name, its docstring and the remaining tactic steps
(source lines 34–38 and 41–53) are kept.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright
2026 Naganori Yamaguchi, author "Naganori Yamaguchi (assisted by OpenAI
Codex)", Apache-2.0. The Lean file carries the dated modification record.
Worker 5168 adapted this proof from the pinned original and wrote the
private helpers following the cited source passages. The published
statement and definitions and their Markdown are used unchanged.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are listed in
`repository_paths`. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This proves only M012.001. The private helpers are not published results.
They do not discharge M008.019, M008.023, M009.006, M009.007, M009.010 or
M009.012, whose exact theorems remain with their own tasks. This module
discharges no class-formation, cup-product, Tate, transfer or reciprocity
target.
