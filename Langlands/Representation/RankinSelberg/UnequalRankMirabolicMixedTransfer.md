# Mixed transfer through unnormalized `Φ⁻`

Module `Langlands.Representation.RankinSelberg.UnequalRankMirabolicMixedTransfer`,
namespace `Langlands.RankinSelberg.UnequalRankMixedTransfer`.

This is a helper module for the proof of
`Langlands.RankinSelberg.UnequalRankMirabolicPairingRigidityStatement`
(JPSS 1983, Section 2.11, Lemma on printed p.399). It states no new
proposition. Its results are internal. It handles the base case of adjacent
ranks `r = n + 1` when the mirabolic representation is radical-generated. In
that case a pairing between `ξ` (a representation of `P_(n+1) ⊂ GL_(n+2)`) and
`η` (a representation of `GL_(n+1)`) becomes a pairing between `Φ⁻ ξ` and the
restriction of `η` to `P_n ⊂ GL_(n+1)`. JPSS make the same reduction with the
classification of `P_(n+1)`-representations. Here it is a direct integral
transform.

The construction adapts the published proof of
`Langlands.Derivative.Mirabolic.phiMinusPairingTransfer`
(`Derivative/MirabolicMinusPairingTransferProof`). That theorem pairs two
representations of the same mirabolic group. Here the second representation
lives on `GL_(n+1)`. Only the three lemmas that use the Levi law are rewritten:
`transferIntegral_levi_mixed`, `exists_open_subgroup_coefficient_mixed` and
`exists_coefficient_support_mixed`. Everything else is a published lemma from
that proof module (`transferIntegral`, `transferForm`,
`transferIntegral_radical_left`, `exists_latticeBox_fixes`,
`exists_mulVec_eq_add`, `exists_integral_character_ne_zero`, `mulVec_last`,
`rep_radicalElement_mul`) or from `RankinSelberg/EqualRankFrobeniusProof`
(`detOne`, `determinantWeight_eq_one`, `determinantWeight_one_sub`,
`exists_lastRow_eq`, `abv_det_inv_mul`).

## Notation

`P_(n+1) = mirabolic (n + 1) F`, with Levi embedding `levi : GL_(n+1) → P_(n+1)`
and radical elements `radicalElement c` for `c ∈ F^(n+1)`. `|·|` is
`normalizedAbsoluteValue T`, and `dW g s = determinantWeight |·| g s = |det g|^s`.
`μ` is an additive Haar measure on `F^(n+1)`. `Φ⁻` is the published unnormalized
functor `phiMinusUnnormalized T ψ n`. Its radical character is
`Θ = T.mirabolicTheta ψ n`, with `Θ(radicalElement c) = ψ(c_last)`
(`theta_radicalElement`).

## Statements

`transferIntegral_levi_mixed`: let `β : V × W → ℂ` be bilinear with
`β(ξ(levi g) v, η(g) w) = dW g (-s) · β(v, w)` and continuous radical
coefficients `c ↦ β(ξ(radicalElement c) v, w)`. Suppose that
`k ↦ μ(k⁻¹ ·)` scales `μ` by `|det k|⁻¹`. Then the published
`transferIntegral μ ψ ξ β`, that is

```text
I(v, w) = ∫ ψ(-c_last) β(ξ(radicalElement c) v, w) dμ(c),
```

satisfies

```text
I(ξ(levi g) v, η(g) w)
  = dW g (-s) · |det g| · ∫ ψ(-(g c)_last) β(ξ(radicalElement c) v, w) dμ(c).
```

Proof: `radicalElement c · levi g = levi g · radicalElement (g⁻¹ c)`
(`levi_mul_radicalElement`). Apply the Levi law and change variables
`c ↦ g⁻¹ c` with the Haar scaling.

`exists_open_subgroup_coefficient_mixed`: for smooth `ξ`, `η`, and fixed `x, w`,
there is an open subgroup `H ⊂ GL_(n+1)` with
`β(ξ(radicalElement (k c)) x, w) = β(ξ(radicalElement c) x, w)` for `k ∈ H`. The
subgroup is `H = levi⁻¹(K₁) ∩ K₂ ∩ {|det| = 1}`, where `K₁` fixes `x` and `K₂`
fixes `w`. Then use the Levi law with weight `1`.

`exists_coefficient_support_mixed`: if moreover `ξ` is radical-generated, each
radical coefficient `c ↦ β(ξ(radicalElement c) v, w)` vanishes outside some
lattice box. The vectors with this property form a submodule. It contains every
`ξ(u) x - x` for `u` in the radical, by the open-subgroup lemma and
`exists_mulVec_eq_add`. Radical generation makes it everything.

`mixedTransfer F T n`: for a unitary character `ψ`, a smooth radical-generated
`ξ` of `P_(n+1)` (with `hs : IsSmooth ξ`), a smooth `η` of `GL_(n+1)`, `s ∈ ℂ`
and a nonzero bilinear `β` with
`β(ξ(levi g) v, η(g) w) = dW g (-s) · β(v, w)` for all `g ∈ GL_(n+1)`, there is
a nonzero

```text
β' ∈ InvariantBilinear.forms (Φ⁻ (ξ, hs)).representation (η|_(P_n))
       (h ↦ dW h (-(s - 1))).
```

Here `η|_(P_n) = η.comp (mirabolic n F).subtype`. The carriers `V` and `W` have
independent universes.

## Proof of `mixedTransfer`

1. Haar scaling for `k ↦ k c` comes from `padicScalarHaarScaling` and
   `haarMeasure_map_matrix`.
2. Radical coefficients are locally constant (`exists_latticeBox_fixes`), so
   they are continuous. By `exists_coefficient_support_mixed` they have compact
   support. So `B = transferForm μ ψ ξ β` is a bilinear form with
   `B(v, w) = I(v, w)`.
3. `transferIntegral_radical_left` gives
   `B(ξ(radicalElement d) v, w) = ψ(d_last) B(v, w)`. Every radical element is
   `radicalElement d` with `Θ = ψ(d_last)`. So `B` factors through the
   `(radical, Θ)`-coinvariants in the first variable
   (`Jacquet.Localization.lift`), and gives `B'` on the carrier of `Φ⁻ ξ`.
4. Covariance. Let `h ∈ P_n`. `Φ⁻` acts by `successor h = levi h`
   (`phiMinusUnnormalized_action`), and `phiMinusQuotient` is surjective.
   `transferIntegral_levi_mixed` with `g = h` and `mulVec_last` (the last row
   of `h` is `e_last`) give
   `B(ξ(levi h) v, η(h) w) = dW h (-s) · |det h| · B(v, w)`. Finally
   `dW h (-s) · |det h| = dW h (-(s - 1))` (`determinantWeight_one_sub`).
5. Nonvanishing. Pick `v₀, w₀` with `β(v₀, w₀) ≠ 0`. The published
   `exists_integral_character_ne_zero` gives a nonzero `y` with
   `∫ ψ(-y·c) β(ξ(radicalElement c) v₀, w₀) dμ(c) ≠ 0`. `exists_lastRow_eq`
   gives `g ∈ GL_(n+1)` with last row `y`. By `transferIntegral_levi_mixed`,
   `B(ξ(levi g) v₀, η(g) w₀)` is this integral times nonzero factors. So
   `B' ≠ 0`.
