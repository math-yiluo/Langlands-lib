# NYLL M009.017–018: targets for the inverse laws of division on `n ℤ̂`

This module extracts two public theorem signatures of Naganori Yamaguchi's
`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean` at pinned
commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The readable original is in the project's literature collection under
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

Both targets are Prop-valued definitions with prefix
`Langlands.NYLL.ClassFormation`. They concern the actual published
`zHatMulNat n : ContinuousAddMonoidHom ZHat ZHat` (M009.002, `x ↦ n • x` on
the closure model `ZHat` of M008.008) and the division map
`zHatDivide n hn` (M009.016), defined in the imported module
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.Definitions`
as the inverse of the continuous additive equivalence
`zHatMulNatRangeEquiv n hn` (M009.015) between `ZHat` and the range of
`zHatMulNat n`.

| Unit | Source signature lines | Original theorem | Adapted target |
| --- | --- | --- | --- |
| M009.017 | 254–256 | `ClassFormation.zHatMulNat_zHatDivide` | `zHatMulNat_zHatDivideStatement` |
| M009.018 | 263–265 | `ClassFormation.zHatDivide_zHatMulNat` | `zHatDivide_zHatMulNatStatement` |

## Statements

Write `R n := ↥(zHatMulNat n).toAddMonoidHom.range`.

`zHatMulNat_zHatDivideStatement (n : ℕ) (hn : 0 < n) (y : R n) : Prop`
is the equality

```lean
zHatMulNat n (zHatDivide n hn y) = y.1
```

in `ZHat`: multiplying the quotient of `y` by `n` recovers the underlying
profinite integer `y.1` of the element `y` of `n ℤ̂`.

`zHatDivide_zHatMulNatStatement (n : ℕ) (hn : 0 < n) (x : ZHat) : Prop`
is the equality

```lean
zHatDivide n hn ⟨zHatMulNat n x, ⟨x, rfl⟩⟩ = x
```

in `ZHat`: dividing `n • x`, packaged as an element of the range with the
witness `x`, recovers `x`.

Each target keeps the source's explicit binders in order: `n : ℕ`, the
positivity proof `hn : 0 < n`, and then `y` or `x`. Neither has universe
parameters. The positivity hypothesis is required by `zHatDivide` itself.
Both conclusions and their orientations are the source's.

## Modifications

Worker 5264 makes these modifications:

- Extract only the two theorem signatures, with the surrounding namespace and
  the source's noncomputable section (source line 26). Omit the proofs
  (source lines 257–259 and 266–268) and the theorem-only `@[simp]`
  attributes (lines 253 and 262).
- Prefix the namespace `ClassFormation` with `Langlands.NYLL` and append
  `Statement` to each theorem name. Each theorem's conclusion becomes the
  body of a `Prop`-valued definition with the same parameters.
- Rephrase the docstrings as target descriptions that keep the source's
  displayed identities.
- Replace the source imports with the single sibling definition module
  `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.Definitions`,
  which supplies `zHatDivide` and transitively `ZHat` and `zHatMulNat`.
- Retain the original copyright, Apache-2.0 and author header, and add the
  explicit modification record in the Lean module documentation.

The module supplies no proofs. Proofs of the two targets are separate units.

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
