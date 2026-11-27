# Square integrability and pairing of the ambient profile lift

Module `Langlands.Global.AdelicWavePacketProductPairing` proves
`Langlands.Global.WavePacketProductPairingStatement` (module
[`Langlands.Global.AdelicWavePacketProductPairingStatement`](AdelicWavePacketProductPairingStatement.md))
unconditionally.

| Declaration | Kind | Content |
| --- | --- | --- |
| `wavePacketProductPairing` | theorem (proved) | `WavePacketProductPairingStatement` |

## The statement

Let `G` be an affine, locally finite type, connected reductive group scheme over a number
field `F`, `eG : ℝ^m ≃ X^*(G) ⊗ ℝ` a linear chart of the ambient real character space and
`b` a smooth compactly supported coefficient on `ℝ^m` with `b ≠ 0`. The lift
`ambientProfileQuotientLift hG eG b f` of a function `f : [G] → ℂ` to `G(F) \ G(𝔸)` sends a
class `q` to `ambientWavePacketProfile eG b a · f(y)`, where `(a, y) ∈ A_G × [G]` is the image
of `q` under `principalQuotientProductEquiv F G hG`. Put
`c = ∫_{A_G} ‖ambientWavePacketProfile eG b a‖² da` for `positiveCentreHaarMeasure F G hG`.
The statement has four clauses:

1. `0 < c`;
2. for every `f` and every `g ∈ G(𝔸)`, the lift at the class of `g` in `G(F) \ G(𝔸)` is
   `ambientWavePacketProfile eG b g · f([g])`, with `[g]` the class of `g` in `[G]`;
3. for every `f : [G] → ℂ`, with no measurability assumption, the lift is in
   `L²(rationalQuotientHaarMeasure F G)` if and only if `f` is in `L²(canonicalMeasure F G)`;
4. for `f, f'` in `L²(canonicalMeasure F G)`, the integral of `lift f · conj (lift f')`
   against `rationalQuotientHaarMeasure F G` is `c` times the integral of `f · conj f'`
   against `canonicalMeasure F G`.

The measures are the Library's fixed ones; the proof rescales none of them.

## The proof

The proof is one term:
`wavePacketProductPairing_of_productMeasure RestrictionSplitCentre.principalQuotientProductMeasure`.

- `Langlands.Global.wavePacketProductPairing_of_productMeasure` (module
  `Langlands.Global.AdelicWavePacketProductPairingProof`) proves
  `PrincipalQuotientProductMeasureStatement → WavePacketProductPairingStatement`.
- `Langlands.Global.RestrictionSplitCentre.principalQuotientProductMeasure` (module
  `Langlands.Global.AdelicPrincipalQuotientMeasure`) proves
  `PrincipalQuotientProductMeasureStatement`: the measurable equivalence
  `principalQuotientProductEquiv F G hG : G(F) \ G(𝔸) ≃ A_G × [G]` carries
  `rationalQuotientHaarMeasure F G` to
  `(positiveCentreHaarMeasure F G hG).prod (canonicalMeasure F G)`, with no constant
  between the two sides.

The conditional theorem works as follows; its Markdown gives the details. Write `A` for the
restriction of the profile to `A_G` and `α`, `ν` for the two factor measures.

- Clause 1: `ambientWavePacketProfile_squareIntegrable` (module
  `Langlands.Global.AdelicAmbientWavePacketProfileProof`) shows that `A` is in `L²(α)` and that
  `c > 0` when `b ≠ 0`.
- Clause 2: a point `g` is written `a · n` with `a ∈ A_G` and `n ∈ G(𝔸)¹`. The equivalence sends
  the class of `g` to `(a, [n])`, and `[n] = [g]` in `[G]`. The profile depends on `g` only
  through `H_G(g)`, and `H_G(g) = H_G(a)` because `H_G` vanishes on `G(𝔸)¹`.
- Clause 3: since the equivalence preserves the measures, the lift is in `L²` exactly when
  `(a, y) ↦ A(a) f(y)` is in `L²(α.prod ν)`. For measurable `f`, Tonelli factors the square
  integral as `(∫ ‖A‖² dα) · (∫ ‖f‖² dν)`, and the first factor is finite and nonzero. For the
  converse, measurability of the product passes to almost every section `y ↦ A(a) f(y)`, and
  since `A` is not almost everywhere zero some section has `A(a) ≠ 0`; dividing by `A(a)` shows
  that `f` is almost everywhere strongly measurable.
- Clause 4: the pairing becomes `∫ ‖A(a)‖² · f(y) conj f'(y) d(α.prod ν)`, which the product
  integral factors as `c · ∫ f conj f' dν`.

`wavePacketProductPairing` depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Sources

The theorem is not numbered in the literature. It compares the quotient conventions of two
sources, as the page of `Langlands.Global.AdelicWavePacketProductPairingStatement` explains:

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*,
  Clay Math. Proc. 13 (2011), §3, Proposition 2, printed p. 314 (PDF p. 323): wave packets on
  `G(F) \ G(𝔸)` and their inner product. Source ID
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`, file SHA-256
  `760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`.
- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations* (2024), §2.6,
  (2.19)–(2.22) and Lemma 2.6.2, printed pp. 68–69 (PDF pp. 85–86): `G(𝔸)¹`, `A_G`,
  `A_G G(𝔸)¹ = G(𝔸)` with `A_G ∩ G(𝔸)¹ = 1` for a number field, and `[G] = A_G G(F) \ G(𝔸)`;
  and §10.5, (10.22)–(10.24), printed pp. 281–282 (PDF pp. 293–294): wave packets on `[G]`.
  Source ID `getz-hahn-2024-automorphic-representations`, file SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.

The proof is measure theoretic: it uses the product decomposition of the quotient and the
square integrability of the profile, and no property of Eisenstein series.
