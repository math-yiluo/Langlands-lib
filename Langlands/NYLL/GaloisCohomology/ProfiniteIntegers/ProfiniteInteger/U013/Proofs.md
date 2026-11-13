# Additive subgroups of `ℤ̂` with a specified positive index

This module proves the published proposition
`Langlands.NYLL.ClassFormation.zHatAddSubgroup_eq_mulNat_range_of_index_eqStatement`
(NYLL unit M009.013) with the theorem
`Langlands.NYLL.ClassFormation.zHatAddSubgroup_eq_mulNat_range_of_index_eq`.

The theorem has the same binders as the target and the source theorem, in the
same order: explicit `(H : AddSubgroup ZHat)`, implicit `{n : ℕ}`, then explicit
`(hn : 0 < n)` and `(hindex : H.index = n)`. Its type is exactly the target
applied to these parameters:

```lean
theorem zHatAddSubgroup_eq_mulNat_range_of_index_eq
    (H : AddSubgroup ZHat) {n : ℕ} (hn : 0 < n) (hindex : H.index = n) :
    zHatAddSubgroup_eq_mulNat_range_of_index_eqStatement H hn hindex
```

Unfolded, the target says `H = (zHatMulNat n).toAddMonoidHom.range`. In words:
an additive subgroup of `ℤ̂` of index `n > 0` is the subgroup `n ℤ̂`. There is
no closedness assumption on `H`, and the proof does not use one.

## Imports and unchanged Library files

The only direct import is
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements`.
Through it the proof uses these published objects, unchanged: the closure model
`ZHat` and its internal pieces `d004`, `d006`, `d007` from
`ProfiniteIntegerCore.Definitions`, the reduction `zHatReduction`, and the
multiplication map `zHatMulNat n : x ↦ n • x` from `ProfiniteInteger.U002.Definitions`.
Everything else comes from Mathlib (subgroup index, quotient by a kernel, density
and closures). The target's Lean/Markdown pair and every pair it imports are
unchanged.

## Mathematical argument

Write `R = n ℤ̂` for the image of `zHatMulNat n` and `K` for the kernel of
reduction modulo `n`.

1. `R ≤ H`. For any `x`, `H.index • x ∈ H`. This holds because the quotient
   `ℤ̂ ⧸ H` is a group of order `H.index`. Since `H.index = n`, every `n • x`
   lies in `H`.
2. `K ⊆ R`. The set `K` is open, because it is the preimage of `{0}` under a
   continuous map to the discrete group `ZMod n`. The image of `ℤ` is dense in
   `ℤ̂`. An integer `a` in `K` satisfies `(a : ZMod n) = 0`, so `a = n * b` for
   an integer `b`, and then `(a : ℤ̂) = n • (b : ℤ̂) ∈ R`. Next, `R` is closed,
   since it is the continuous image of the compact space `ℤ̂` in a Hausdorff
   space. Every point of the open set `K` lies in the closure of `K ∩ ℤ`, and
   that closure lies in the closed set `R`.
3. `R = K`, and `R` has index `n`. If `y = n • x`, its reduction is
   `n · (x mod n) = 0` in `ZMod n`, so `R ≤ K`. Together with step 2 this gives
   `R = K`. Every class in `ZMod n` is the reduction of an integer, so reduction
   is surjective. Hence `ℤ̂ ⧸ K ≃ ZMod n` and `R.index = K.index = n`.
4. Conclusion. Since `R ≤ H`, the relative index satisfies
   `R.relIndex H * H.index = R.index`, that is, `R.relIndex H * n = n`. Because
   `n > 0`, the relative index is `1`, which means `H ≤ R`. Together with step 1,
   `H = R`.

## Implemented Lean proof

The module has three `private` lemmas and the public theorem. The lemmas are
local to this file and do not claim any other published target.

- `u013_denseRange_intCast : DenseRange (Int.castRingHom ZHat)`. `himg` shows that
  the image under `Subtype.val` of the integer casts in `d007` is the carrier of
  the integer subring `d006` inside the ambient product `d004`. Both inclusions
  are elementwise `rfl` computations of the diagonal integer cast. Density then
  follows from `Topology.IsInducing.subtypeVal.dense_iff`: every `x : d007`
  satisfies `x.1 ∈ closure (d006 : Set d004)`. This is exactly the membership
  proof `x.2`, because `d007` is the subtype of `d006.topologicalClosure`. The
  goal is rewritten back with `himg`.
- `u013_ker_le_range n hn`, step 2. Openness of `K` uses `isOpen_discrete` and
  `map_continuous (zHatReduction n hn)`. Closedness of `R` uses
  `AddMonoidHom.coe_range`, `isCompact_range` and `IsCompact.isClosed`. For
  `K ∩ range ⊆ R`, membership in the kernel of an integer cast is definitionally
  `(a : ZMod n) = 0`. `ZMod.intCast_zmod_eq_zero_iff_dvd` gives `a = n * b`, with
  witness `(b : ZHat)`; the identity `n • (b : ZHat) = ((n * b : ℤ) : ZHat)` is
  closed by `nsmul_eq_mul`, `Int.cast_mul` and `Int.cast_natCast`. The conclusion
  is `closure_minimal` applied to `Dense.open_subset_closure_inter`.
- `u013_range_index n hn`, step 3. `hrange : R = K` is proved by `le_antisymm`.
  The inclusion `R ≤ K` uses `map_nsmul`, `nsmul_eq_mul` and `ZMod.natCast_self`;
  the reverse inclusion is the previous lemma. Surjectivity of reduction comes
  from `ZMod.intCast_surjective`, with the integer cast as the preimage (definitionally
  `rfl`). The index is computed by rewriting `AddSubgroup.index`, then
  `Nat.card_congr` with the equivalence
  `QuotientAddGroup.quotientKerEquivOfSurjective`, then `Nat.card_zmod`.
- `zHatAddSubgroup_eq_mulNat_range_of_index_eq`, steps 1 and 4. `change` unfolds
  the target. `hle : R ≤ H` comes from `AddSubgroup.nsmul_index_mem`, rewritten by
  `hindex`. `AddSubgroup.relIndex_mul_index hle` is rewritten by
  `u013_range_index n hn` and `hindex` to `R.relIndex H * n = n`, and
  `Nat.eq_of_mul_eq_mul_right hn` gives `R.relIndex H = 1`. The proof ends with
  `le_antisymm (AddSubgroup.relIndex_eq_one.mp hrel) hle`.

The Lean service's development check compiled this module with Lake with no
errors or warnings. It reported the axioms `propext`, `Classical.choice` and
`Quot.sound` only.

## Source correspondence and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean` (SHA-256
`b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`). A copy is kept at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`.
Lines 214–215 are the docstring, which is retained. Lines 216–218 are the
signature; lines 219–221 are the proof. The source proof runs `subst n` and then
applies `zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero` (M009.012,
lines 195–212).

M009.012 is not proved in the Library at the workspace base
`9b849caba7c63ede041b7fec49c90ceaafb08568`; its focused Task 5767 is unclaimed.
Neither are the facts it depends on: M009.010, M009.011 and the core density
theorem M008.023. The task context allows an alternative exact proof from
published data and Mathlib, so this module proves the target directly. The
private lemmas correspond to source declarations as follows.

| Source declaration (pinned lines) | Here |
| --- | --- |
| `denseRange_intCast_zHat`, `Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean` 170–196 (file SHA-256 `a6cdc6d3cfca209257868daa4e1aa09ca4f83d08927114958d2737b93b309ae5`), M008.023 | `u013_denseRange_intCast`. It uses a different route: `IsInducing.subtypeVal.dense_iff` and the subtype's membership proof replace the source's composition of `denseRange_inclusion_iff` with `rangeRestrict`. |
| `zHatMulNat_range_eq_ker_reduction`, inclusion `K ≤ R`, lines 149–172 (M009.010) | `u013_ker_le_range`. It is the same density argument. `isClosed_zHatMulNat_range` (lines 105–108) is inlined, and `zHatMulNat_int` (lines 130–136) is replaced by a ring computation in `ZHat`, with no `ZHat.ext`. |
| `zHatMulNat_range_eq_ker_reduction`, inclusion `R ≤ K` (lines 145–148), and `zHatMulNat_range_index` (lines 175–189, M009.011) | `u013_range_index`. The index is computed through `quotientKerEquivOfSurjective`, not through `AddSubgroup.index_ker` and `range_eq_top_of_surjective`. Surjectivity (`zHatReduction_surjective`, lines 119–123) is inlined. |
| `zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero` body, lines 198–212 (M009.012) | The body of the main theorem. It is the same `nsmul_index_mem`, `relIndex_mul_index`, `relIndex_eq_one` argument, with `H.index` replaced by `n` through `hindex` rather than `subst`. |

Other adaptations: the namespace gets the prefix `Langlands.NYLL`; the theorem's
stated type is the published Statement applied to the source parameters; the
source imports are replaced by the one published Statements import; and the three
helpers are file-private, so their names do not collide with future exact proofs
of M008.023, M009.010, M009.011 or M009.012. After those publications, a
maintainer could replace this proof with the source's two-line reduction to
M009.012 without changing the theorem.

The retained source is registered as `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
In the public partition
[notes/reuse/nyll-public-port/m001-m024.md](../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m009),
M009.013 is listed at source line 216.

## Attribution, environment and scope

The Lean file keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0
and author header verbatim, including "Naganori Yamaguchi (assisted by OpenAI
Codex)". Worker 135's dated modification record follows it. Worker 135 wrote this
proof and companion from the pinned original, the published statement and
definitions, and Mathlib. No other worker's draft was reused, and there are no
project coauthors. The unchanged inherited
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) have SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. They are listed in
`repository_paths`.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`: Lean 4.34.0 and
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. A development compilation is not
acceptance. Publication under `lean.proof@1` requires the Lake, kernel,
exact-target and unchanged-statement checks, independent semantic review, and
Integrator publication.

This module proves only M009.013. It publishes no exact proof of M008.023,
M009.010, M009.011, M009.012 or M009.014, and it asserts no host class-formation
or reciprocity result.
