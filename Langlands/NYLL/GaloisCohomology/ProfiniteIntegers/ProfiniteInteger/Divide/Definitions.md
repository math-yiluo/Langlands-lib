# NYLL M009.015–016: the range equivalence and division on `n ℤ̂`

This file adapts two definitions of Naganori Yamaguchi's
`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean` at pinned
commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The readable original is in the project's literature collection under
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

| Unit | Source lines (declaration line) | Original name | Adapted name |
| --- | --- | --- | --- |
| M009.015 | 231–246 (232) | `ClassFormation.zHatMulNatRangeEquiv` | `Langlands.NYLL.ClassFormation.zHatMulNatRangeEquiv` |
| M009.016 | 247–250 (248) | `ClassFormation.zHatDivide` | `Langlands.NYLL.ClassFormation.zHatDivide` |

The dependencies are the published `Langlands.NYLL.ClassFormation.ZHat`
(M008.008, the actual closure model of the profinite integers in `Type 0`,
with its published compact Hausdorff topology), the continuous additive map
`Langlands.NYLL.ClassFormation.zHatMulNat` (M009.002, `x ↦ n • x`), and the
published theorem `Langlands.NYLL.ClassFormation.zHatMulNat_injective`
(M009.005), which proves `zHatMulNat_injectiveStatement hn`, that is,
`Function.Injective (zHatMulNat n)` for `0 < n`.

## Telescopes

Both definitions have no universe parameters. Writing
`R n := ↥(Langlands.NYLL.ClassFormation.zHatMulNat n).toAddMonoidHom.range`
for the additive subgroup `n ℤ̂` as a type, the types are

```lean
Langlands.NYLL.ClassFormation.zHatMulNatRangeEquiv :
  (n : ℕ) → 0 < n → Langlands.NYLL.ClassFormation.ZHat ≃ₜ+ R n

Langlands.NYLL.ClassFormation.zHatDivide :
  (n : ℕ) → 0 < n → ContinuousAddMonoidHom (R n) Langlands.NYLL.ClassFormation.ZHat
```

Both keep the source's explicit `n : ℕ` followed by the explicit positivity
proof `hn : 0 < n`. No closedness, finiteness or other hypothesis is added.

## Constructions

`zHatMulNatRangeEquiv n hn` is the source construction, unchanged. It first
forms the additive equivalence
`AddMonoidHom.ofInjective (zHatMulNat_injective hn)` of `ZHat` with the range
of multiplication by `n`, which sends `x` to `⟨zHatMulNat n x, ⟨x, rfl⟩⟩`.
It proves this map continuous by `Continuous.subtype_mk` applied to the
continuity of `zHatMulNat n`. Because `ZHat` is compact and the range is
Hausdorff, Mathlib's `Continuous.homeoOfEquivCompactToT2` turns the equivalence
into a homeomorphism. The result is the additive equivalence with the
continuity fields `continuous_toFun` and `continuous_invFun` taken from that
homeomorphism and its inverse. Its underlying function is therefore
multiplication by `n`, corestricted to its range.

`zHatDivide n hn` is the inverse `(zHatMulNatRangeEquiv n hn).symm`, viewed as
a continuous additive monoid homomorphism through Mathlib's coercion of a
continuous additive equivalence. It sends an element `y` of `n ℤ̂` to the
unique `x : ZHat` with `n • x = y`.

The inverse laws M009.017 and M009.018 are stated as separate targets in the
sibling module
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.Statements`.
This module proves no theorem about these maps.

## Modifications

Worker 5264 makes these modifications:

- Extract only M009.015 and M009.016, with the surrounding namespace and the
  source's noncomputable section (source line 26). Omit all other source
  declarations and narrow the module documentation to these definitions.
- Prefix the source namespace `ClassFormation` with `Langlands.NYLL`. The
  declaration names, docstrings, `noncomputable` modifiers, telescopes,
  result types and construction bodies are unchanged.
- Replace the source imports (four Mathlib modules and
  `Nyll.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore`) with the
  single published module
  `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U005.Proofs`.
  It contains the proof of M009.005 that the construction uses, and it
  transitively imports `ZHat`, its compact Hausdorff topology, `zHatMulNat`
  and the Mathlib API that the construction needs.
- Retain the original copyright, Apache-2.0 and author header, and add the
  explicit modification record in the Lean module documentation.

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
