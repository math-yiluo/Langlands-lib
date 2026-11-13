# Injectivity of multiplication by a positive natural number on `ℤ̂`

This module proves the independently published proposition
`Langlands.NYLL.ClassFormation.zHatMulNat_injectiveStatement` by the theorem
`Langlands.NYLL.ClassFormation.zHatMulNat_injective`. Its type is

```lean
theorem zHatMulNat_injective {n : ℕ} (hn : 0 < n) :
    zHatMulNat_injectiveStatement hn
```

that is, the named target applied to the source parameters: implicit
`n : ℕ` followed by explicit `hn : 0 < n`. No new parameter, divisibility
assumption, inverse map or instance is added.

Its sole direct import is
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements`.
That published Lean/Markdown pair and the pairs it imports
(`ProfiniteInteger.U002.Definitions`, `ProfiniteIntegerCore.Definitions`) are
unchanged. The proof uses their existing definitions and Mathlib lemmas only;
no M008 or M009 theorem proof is imported, because none needed here is in the
Library at the workspace base `9b849caba7c63ede041b7fec49c90ceaafb08568`.

## Target and mathematical meaning

Unfolding the published proposition gives

```lean
Function.Injective (zHatMulNat n)
```

where `zHatMulNat n : ContinuousAddMonoidHom ZHat ZHat` is the published
map `x ↦ n • x` (M009.002) and `ZHat` is the published Type-zero closure
model (M008). In that model `ZHat` is, by definition, the topological closure
`d007` of the subring `d006`, the range of the diagonal ring map
`d005 : ℤ →+* d004`, inside the product `d004 = ∀ i : d001, ZMod i.modulus`
over all positive moduli. Each `ZMod k` has the discrete topology. The
reduction `zHatReduction k hk x` is the coordinate of `x` at the index
`d003 k hk = ⟨k, hk⟩`.

Mathematically: if `n • x = n • y` with `n > 0`, then for every positive
modulus `m`, reducing modulo `n * m` gives `n • x̄ = n • ȳ` in
`ZMod (n * m)`. Hence `n * m` divides `n * (a - b)` for integer
representatives `a`, `b`, so `m` divides `a - b` and `x̄`, `ȳ` agree modulo
`m`. The modulus-`m` reduction is the image of the modulus-`n * m` reduction,
so `x` and `y` have the same reduction at every positive modulus, and are
therefore equal.

## Implemented proof

The module contains four declarations.

1. `Langlands.NYLL.PortInternal.M009.d004` is the source private helper
   M009.004 `zmod_cast_eq_of_nsmul_eq`, with its full source telescope
   (implicit `n m : ℕ`, explicit `hn : 0 < n`, implicit
   `a b : ZMod (n * m)`, explicit `h : n • a = n • b`) and its source body
   verbatim. Its conclusion is the equality of the images of `a` and `b`
   under `ZMod.castHom` for `m ∣ n * m`. The proof lifts `a`, `b` to
   integers with `ZMod.intCast_surjective`, rewrites the casts by
   `ZMod.cast_intCast`, reduces the goal to `(m : ℤ) ∣ a - b` with
   `ZMod.intCast_zmod_eq_zero_iff_dvd`, derives
   `((n * m : ℕ) : ℤ) ∣ n * (a - b)` from `h`, and cancels the nonzero
   factor `n` with `mul_dvd_mul_iff_left`.
2. `zHat_ext_of_reductions` (private) states that `x y : ZHat` are equal
   when `zHatReduction k hk x = zHatReduction k hk y` for every `k` and
   `hk : 0 < k`. The proof views `x`, `y` as elements of the subtype `d007`,
   applies `Subtype.ext` and `funext` over the index type `d001`, and uses
   the hypothesis at `i.modulus`, `i.positive`; the index `d003 i.modulus
   i.positive` is `i` by structure eta.
3. `zHatReduction_transition_of_closure` (private) states that for
   `hm : 0 < m`, `hn : 0 < n`, `hmn : m ∣ n` and `x : ZHat`,
   `ZMod.castHom hmn (ZMod m) (zHatReduction n hn x) = zHatReduction m hm x`.
   The set `S` of `f : d004` with
   `ZMod.castHom hmn (ZMod m) (f (d003 n hn)) = f (d003 m hm)` is closed by
   `isClosed_eq`, since both sides are continuous (coordinate projections,
   and `ZMod.castHom` on a discrete space via
   `continuous_of_discreteTopology`) into the Hausdorff space `ZMod m`.
   Every element `d005 a` of `d006` lies in `S` by `map_intCast` for the
   ring homomorphism `ZMod.castHom hmn (ZMod m)`. By `closure_minimal`, the
   closure `d007` lies in `S`, and the membership proof carried by `x`
   gives the claim.
4. `zHatMulNat_injective` first restates the goal as
   `Function.Injective (zHatMulNat n)` with `show`, then follows source
   lines 91–102: introduce `x`, `y`, `hxy`, apply extensionality (step 2),
   fix a positive modulus `m`, form `hnm : 0 < n * m` and
   `hdiv : m ∣ n * m`, derive
   `hj : n • zHatReduction (n * m) hnm x = n • zHatReduction (n * m) hnm y`,
   rewrite both sides of the goal backwards by the transition lemma
   (step 3) at modulus `n * m`, and conclude with `d004 hn hj` (step 1).
   The proofs of `m ∣ n * m` in the goal and in `d004` are equal by proof
   irrelevance.

Differences from the source proof of M009.005 (lines 88–102):

- Source line 92 applies M008.021 `ZHat.ext`, and lines 100–101 rewrite by
  M008.022 `zHatReduction_transition`. Only their targets
  (`ZHat.extStatement`, `zHatReduction_transitionStatement`) are in the
  Library at the workspace base, so the private lemmas of steps 2 and 3 are
  used instead. Their hypotheses and conclusions are those of the two
  M008 source theorems (in step 3 the transition lemma has the source's
  binder order `m n`, `hm hn hmn x`), but they are private to this module
  and are not offered as proofs of the M008 targets.
- Source lines 98–99 derive `hj` by
  `simpa only [zHatMulNat_apply, map_nsmul] using congrArg ...`. The
  M009.003 evaluation theorem `zHatMulNat_apply` is not yet published, so
  `hj` is proved by rewriting with `map_nsmul` backwards and closing with
  the same `congrArg` term; this uses that `zHatMulNat n x` is by definition
  `n • x`, which is exactly the content of M009.003 (proved by `rfl` in the
  source).

The development check of the Lean service compiled this module with no
errors or warnings, and the Lake build reported the axioms `propext`,
`Classical.choice` and `Quot.sound` only.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean#L64-L102),
retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`
with whole-file SHA-256
`b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`
(recomputed by Worker 79 on 13 November 2026 UTC). Lines 64–86 are the
private helper M009.004; lines 88–102 are M009.005 with its docstring at
line 88 and signature at lines 89–90.

| Original in `ClassFormation` | Adapted in this module |
| --- | --- |
| Private `zmod_cast_eq_of_nsmul_eq` (M009.004, lines 64–86) | `Langlands.NYLL.PortInternal.M009.d004`, same telescope and body |
| Asserted type of `zHatMulNat_injective` (lines 89–90) | Published `Langlands.NYLL.ClassFormation.zHatMulNat_injectiveStatement` |
| Proof `zHatMulNat_injective` (lines 91–102) | `Langlands.NYLL.ClassFormation.zHatMulNat_injective` |
| `ZHat.ext` (M008.021, used at line 92) | Private `zHat_ext_of_reductions`, proved here |
| `zHatReduction_transition` (M008.022, used at lines 100–101) | Private `zHatReduction_transition_of_closure`, proved here |
| `zHatMulNat_apply` (M009.003, used at line 98) | Not used; definitional evaluation of `zHatMulNat` |

The name `PortInternal.M009.d004` follows the
[public partition](../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m009),
which lists M009.004 with that prospective declaration and places M009.005
after it. The task context allows proving this helper inside the M009.005
candidate. The partition's later M009.015 `zHatMulNatRangeEquiv`
(source line 235) uses `zHatMulNat_injective`.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution, imports, modifications and scope

The Lean file keeps the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 79's dated modification
record. Modifications: the `Langlands.NYLL` namespace prefix; the source
imports (`Mathlib.SetTheory.Cardinal.Finite`, `Mathlib.Topology.Neighborhoods`,
`Mathlib.Algebra.Group.Subgroup.Ker`, `Mathlib.GroupTheory.Index`,
`Nyll.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore`) replaced by
the sole published Statements import; the helper renamed to its port-internal
name and made public; the theorem stated as the published proposition; and
the three replacements listed above. Worker 79 wrote this proof and companion
directly from the pinned original and the published statement and
definitions; no other worker's draft was reused, and there are no project
coauthors.

The unchanged inherited [LICENSE](../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../licenses/NYLL/NOTICE) are retained in
`repository_paths`. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake/kernel/exact-target and unchanged-statement
checks, independent semantic review and Integrator publication.

This proof covers only M009.005 together with the M009.004 helper. It does
not prove the published M008.021, M008.022 or M009.003 targets, nor any
other M009 target, and asserts no host class-formation or reciprocity
result.
