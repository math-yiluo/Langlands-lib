# NYLL M009.018: division after multiplication on `ℤ̂`

`Langlands.NYLL.ClassFormation.zHatDivide_zHatMulNat` proves exactly
`Langlands.NYLL.ClassFormation.zHatDivide_zHatMulNatStatement n hn x` for
`n : ℕ`, `hn : 0 < n`, and `x : ZHat`. It asserts

```lean
zHatDivide n hn ⟨zHatMulNat n x, ⟨x, rfl⟩⟩ = x
```

The range element carries its actual preimage witness `x`.

## Source and attribution

The source is Naganori Yamaguchi's
`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`, at commit
`fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. Its SHA-256 is
`b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The readable source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

The original 2026 copyright and author header (Naganori Yamaguchi,
assisted by OpenAI Codex) is retained. The existing Apache-2.0
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain applicable and
unchanged. Worker 356 extracts this proof for its published target.

The source theorem is lines 263–268, with `@[simp]` at line 262.

## Implemented proof and dependencies

The `change` unfolds the target and division and recognizes the displayed
range element as `(zHatMulNatRangeEquiv n hn) x`. The goal becomes

```lean
(zHatMulNatRangeEquiv n hn).symm ((zHatMulNatRangeEquiv n hn) x) = x
```

The equivalence's `symm_apply_apply x` proves it directly. This is exactly
the source proof route, including the canonical range witness.

The only direct import is the unchanged published
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.Statements`.
It imports `Divide.Definitions`, which supplies M009.015
`zHatMulNatRangeEquiv` and M009.016 `zHatDivide`. Those definitions retain
the source's actual continuous additive equivalence between `ZHat` and
the range of M009.002 `zHatMulNat n`, with inverse `zHatDivide n hn`.
They transitively use the published injectivity theorem M009.005 to
construct the equivalence. The present proof uses its inverse law and
introduces no further assumptions.

## Modifications

The source namespace receives the `Langlands.NYLL` prefix. The broad source
imports are replaced by the focused published statement module. The theorem
concludes the exact named target proposition, with the original explicit
binders in their original order and no universe parameters. Its proof body
is the original proof. The source `@[simp]` attribute is omitted because the
theorem is stated through the opaque target proposition. No published
statement or definition is edited.
