# NYLL M009.010: multiplication image and reduction kernel

The theorem `Langlands.NYLL.ClassFormation.zHatMulNat_range_eq_ker_reduction`
proves the published target
`Langlands.NYLL.ClassFormation.zHatMulNat_range_eq_ker_reductionStatement n hn`.
Its complete telescope is explicit `(n : ℕ) (hn : 0 < n)`, in that order, with
no further parameters or hypotheses. The target unfolds to

```lean
(zHatMulNat n).toAddMonoidHom.range =
  (zHatReduction n hn).toAddMonoidHom.ker
```

Both maps and `ZHat : Type 0` are the unchanged published source objects.
`ZHat` is the closure of the diagonal integers in the product of the positive
finite residue rings, `zHatMulNat n` acts by `x ↦ n • x`, and reduction is the
coordinate at modulus `n`. The equality is between the actual additive
subgroups, in the multiplication-range to reduction-kernel orientation.

## Implemented proof

The proof applies additive-subgroup extensionality and proves two inclusions.
Reduction of `n • x` is `n •` the reduction of `x`. In `ZMod n`, this vanishes
by the natural scalar multiplication formula and reduction of the modulus.
This gives the range-to-kernel inclusion.

For the reverse inclusion, write `K` for the reduction kernel and `D` for the
range of the ordinary integer cast into `ZHat`. The kernel is open because
reduction is continuous and the singleton zero is open in the discrete ring
`ZMod n`. The theorem `denseRange_intCast_zHat` says that `D` is dense.
An integer `a` whose cast lies in `K` satisfies `(a : ZMod n) = 0`.
`ZMod.intCast_zmod_eq_zero_iff_dvd` gives `(n : ℤ) ∣ a`, so write `a = n * b`.
The theorem `zHatMulNat_int n b` exhibits its cast in the multiplication
range. Thus `K ∩ D` is contained in that range. Mathlib's
`Dense.open_subset_closure_inter` puts every point of `K` in the closure of
`K ∩ D`. Finally, `closure_minimal` and `isClosed_zHatMulNat_range n` give the
required membership. The intermediate arguments introduce no new assumptions.

The integer-reduction computation uses the already published M008.019 theorem
`zHatReduction_intCast n hn a`. Its target unfolds to
`zHatReduction n hn (a : ZHat) = (a : ZMod n)`.
Evaluation of `Int.castRingHom ZHat` at `a` is definitionally `(a : ZHat)`, so
this is the exact formula used by source M009.007 `zHatReduction_int`, with the
same explicit `n`, `hn`, `a` parameter order. The proof changes kernel
membership into reduction equal to zero, then composes the symmetric reduction
formula with this equality. It needs no new alias or simp attribute.

## Source correspondence and modifications

This proof is adapted from Naganori Yamaguchi's
`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, lines 138–172
(signature lines 139–141). The original file SHA-256 is
`b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`.
The full original file was read. It is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Original name in `ClassFormation` | Used name in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| `zHatMulNat_range_eq_ker_reduction` (M009.010) | `zHatMulNat_range_eq_ker_reduction`, proving the existing Statement target |
| `ZHat`, `zHatMulNat`, `zHatReduction` | Same suffixes on the published source model |
| `denseRange_intCast_zHat` (M008.023) | `denseRange_intCast_zHat` |
| `isClosed_zHatMulNat_range` (M009.006) | `isClosed_zHatMulNat_range` |
| `zHatMulNat_int` (M009.009) | `zHatMulNat_int` |
| `zHatReduction_int` (M009.007) | Replaced by the published `zHatReduction_intCast` (M008.019), with exact correspondence above |

Worker 240 adds the `Langlands.NYLL` namespace prefix, extracts this one theorem,
and expresses its type as the exact named Statement target. The proof retains
the original mathematical route. It contracts the open-singleton argument and
the range witness construction, applies integer reduction explicitly instead
of relying on the source simp theorem, and imports focused published proof
modules instead of the whole upstream core module. No prerequisite proof is
copied, and no imported Lean or Markdown file is changed. The original
noncomputable section is unnecessary for this theorem and is omitted.

## Imports and attribution

The direct imports are:

- `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements`,
  for the exact target and multiplication data;
- `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.U019.Proofs`,
  for integer reduction;
- `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.U023.Proofs`,
  for density of integer casts;
- `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U006.Proofs`,
  for closedness of the multiplication range;
- `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U009.Proofs`,
  for integer multiplication;
- `Mathlib.Topology.Neighborhoods`, retained from the original topology imports.

Mathlib supplies subgroup extensionality, continuity and the topology of finite
residue rings, integer divisibility, and the closure lemmas. No Mathlib source
is copied. The environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, as pinned by approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`.

The original copyright, Apache-2.0 notice and author header are retained,
including the attribution to Naganori Yamaguchi (assisted by OpenAI Codex).
The unchanged `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` have hashes
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
This unit proves only M009.010 and asserts no host class-formation or reciprocity
result.
