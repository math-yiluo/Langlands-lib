# L2: normalized level of a twist by `χ ∘ det`

Module `Langlands.BushnellKutzko.NormalizedLevelTwistStatement`, namespace
`Langlands.BushnellKutzko`. Uses `IsNormalizedLevel` and `isOpen_ker_determinantCharacter` from
`Langlands.BushnellKutzko.NormalizedLevel`, the Library's `SmoothDualClass.twist`
(`Langlands/Representation/Category/Twist.lean`), `GeneralLinear.determinant` and
`PadicField.TopologicalData.multiplicativeConductor` (`Langlands/HarmonicAnalysis/Conductor.lean`).

Source: operator route note `operator-numerical-llc-route-2026-11-16`, Lemma `lem:level`(ii),
first sentence, printed p. 16 (the proof is on the same page). **L2 is an internal result of the route note** (marked "[proved here]"), not a
statement from the published literature. The note proves it from L1
(`FundamentalStratumLevelStatement`, Lemma `lem:level`(i)), using `det(1 + 𝔓^j) ⊆
1 + 𝔭^{⌈j/e⌉}` and `det(1 + x) ≡ 1 + tr(x) mod 𝔭^{k+1}` on `U^{e'k}(𝔄')`.

`NormalizedLevelTwistStatement.{uK, uV} : Prop` is an unproved statement; a later
`lean.proof@1` task proves it, and that task needs a proof of L1.

## Statement

For every prime `p`, every `K : PadicField.{uK} p`, every `n ≥ 1`, every quasicharacter
`χ : HarmonicAnalysis.Quasicharacter K.Carrier` (a continuous homomorphism `K^× → ℂ^×`; the
Library's `QuasiCharacter K`), every `k : ℕ` with
`k = K.canonicalTopologicalData.multiplicativeConductor χ - 1` (truncated subtraction in `ℕ`),
every class `a : SmoothDualClass.{0, uK, uV} (k := ℂ) (G := GeneralLinear n K.Carrier)` and all
`x y : ℚ`: if `IsNormalizedLevel K n a x` and `IsNormalizedLevel K n a' y`, where

`a' = SmoothDualClass.twist (χ.toMonoidHom.comp GeneralLinear.determinant)
(isOpen_ker_determinantCharacter K n χ) a`

is the twist of `a` by the character `χ ∘ det` of `GL_n(K)`, then

- `y ≤ max x k`, and
- if `x ≠ k`, then `y = max x k`.

`multiplicativeConductor χ` is Tate's exponent `a(χ)` (`0` exactly for unramified `χ`), so
`k = max(a(χ) − 1, 0)` is the Swan exponent `sw(χ)` of the route note. The openness of the
kernel of `χ ∘ det`, required by `SmoothDualClass.twist`, is the proved lemma
`isOpen_ker_determinantCharacter`, so it is not a hypothesis.

Sanity check: for unramified `χ`, `k = 0`, and `χ ∘ det` is trivial on every `U^1(𝔄)`, so
twisting preserves every fixed-vector condition and `y = x`, consistent with the statement.
