# NYLL M009.006: the image of natural multiplication on ZHat is closed

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.isClosed_zHatMulNat_rangeStatement` by the theorem
`Langlands.NYLL.ClassFormation.isClosed_zHatMulNat_range`. Its type is exactly
that target applied to the single source parameter:

```lean
theorem isClosed_zHatMulNat_range (n : ℕ) :
    isClosed_zHatMulNat_rangeStatement n
```

The parameter `n : ℕ` is explicit and arbitrary, including `n = 0`. There
is no positivity premise and no other hypothesis, instance or universe
parameter.

Its sole direct import is
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements`.
That published Lean/Markdown pair and everything it imports remain
unchanged. The proof also uses Mathlib declarations available through
that import chain. No other M009 or M008 theorem proof is used.

## Target and mathematical meaning

Unfolding the published target gives

```lean
IsClosed ((zHatMulNat n).toAddMonoidHom.range : Set ZHat)
```

`ZHat : Type 0` is the published closure model. It is the topological
closure of the image of `ℤ` in the product `∀ i, ZMod i.modulus` over all
positive moduli, with the subspace topology. `zHatMulNat n` is the published
continuous additive endomorphism `x ↦ n • x` of `ZHat`. The target asserts
that its image `n ℤ̂` is a closed subset of `ZHat`. For `n = 0` the image is
`{0}`; the proof below treats every `n` uniformly.

## Implemented proof

The complete proof body is

```lean
  unfold isClosed_zHatMulNat_rangeStatement
  rw [AddMonoidHom.coe_range]
  exact (isCompact_range (map_continuous (zHatMulNat n))).isClosed
```

1. `unfold` exposes the published `IsClosed` assertion.
2. Mathlib's `AddMonoidHom.coe_range` rewrites the carrier of the range
   subgroup to `Set.range` of the underlying function.
3. `map_continuous (zHatMulNat n)` is the continuity carried by the
   bundled `ContinuousAddMonoidHom`. The underlying function of
   `(zHatMulNat n).toAddMonoidHom` is definitionally that of `zHatMulNat n`,
   so `exact` accepts the term without a further rewrite.
4. Mathlib's `isCompact_range` uses the published instance
   `CompactSpace ZHat` (`Langlands.NYLL.PortInternal.M008.d014`) to make the
   range compact.
5. `IsCompact.isClosed` uses the published instance `T2Space ZHat`
   (`Langlands.NYLL.PortInternal.M008.d012`): a compact subset of a Hausdorff
   space is closed.

No auxiliary declaration, simp attribute or new instance is introduced.
The development check reported no errors or warnings. The theorem's axioms
are `propext`, `Classical.choice` and `Quot.sound`.

## Pinned source and correspondence

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact source passage is
[`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean:104–108`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean#L104-L108).
Line 104 is the docstring, lines 105–106 are the signature, line 107 is
`rw [AddMonoidHom.coe_range]` and line 108 is the closing `exact`. The
whole-file SHA-256 is
`b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`.
The source compactness and Hausdorff instances are at lines 96 and 86 of
`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean`
(SHA-256 `a6cdc6d3cfca209257868daa4e1aa09ca4f83d08927114958d2737b93b309ae5`).
Worker 106 read these source lines and recomputed both hashes on
13 November 2026 UTC.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Signature of `isClosed_zHatMulNat_range` (lines 105–106) | Published `isClosed_zHatMulNat_rangeStatement n` in ProfiniteInteger.Statements |
| Proof `isClosed_zHatMulNat_range` (lines 107–108) | This theorem of the same adapted name in U006.Proofs |
| `ZHat`, its `CompactSpace` and `T2Space` instances | Published closure model and instances `PortInternal.M008.d014`, `d012` |
| `zHatMulNat` (lines 52–56) | Published `zHatMulNat` in ProfiniteInteger.U002.Definitions |

Modifications: the namespace is prefixed with `Langlands.NYLL`; the theorem
type is the published target applied to `n`, so an `unfold` step precedes
the two retained source tactics; the source imports are replaced by the
single published statement import; and the source docstring is extended to
mention the zero case. The source `noncomputable section` is retained.
The [public partition](../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m009)
lists this proof as M009.006.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution, environment and scope

The Lean file keeps the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including "Naganori Yamaguchi
(assisted by OpenAI Codex)". Worker 106's modification record follows it.
There are no project coauthors. The unchanged
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are already in the Library.
Their SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. A development check is not
acceptance: publication under `lean.proof@1` also requires the Lake build,
the exact-target and unchanged-statement checks, independent semantic
review and Integrator publication.

This proof covers only M009.006. It asserts no other M009 target, no host
class-formation result and no reciprocity theorem.
