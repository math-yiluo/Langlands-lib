# Reduction of the supercuspidal twist Swan bound to the level statements

Module `Langlands.Correspondence.HenniartTwistSwanReductionStatement`, namespace
`Langlands.Henniart`. It defines one proposition and proves nothing.

## Statement

`SupercuspidalTwistSwanBoundReductionStatement.{uK, uV} : Prop` is the implication

```
BushnellKutzko.NormalizedLevelExistenceStatement.{uK, uV} →
  BushnellKutzko.NormalizedLevelTwistStatement.{uK, uV} →
    BushnellKutzko.SupercuspidalSwanLevelStatement.{uK, uV} →
      SupercuspidalTwistSwanBoundStatement.{uK, uV}
```

In words: suppose that

- **(L0)** for every prime `p`, every `K : PadicField.{uK} p` and every `n ≥ 1`, every class
  of irreducible admissible complex representations of `GL_n(K)` (carrier universe `uV`)
  has a normalized level `ℓ(π)`
  (`Langlands.BushnellKutzko.NormalizedLevelExistenceStatement`);
- **(L2)** for such a class `π` and every quasicharacter `χ` of `K^×` with Swan exponent
  `sw(χ) = a(χ) − 1` (truncated), the normalized level of the twist `(χ ∘ det) ⊗ π` satisfies
  `ℓ(χπ) ≤ max(ℓ(π), sw(χ))`, with equality when `ℓ(π) ≠ sw(χ)`
  (`Langlands.BushnellKutzko.NormalizedLevelTwistStatement`);
- **(T2)** for every supercuspidal class `π` of `GL_{k+1}(K)` with normalized level `x`,
  the conductor `Numerical.conductor K π` is a natural number `c` and
  `c − (k + 1) = (k + 1) x`, i.e. `sw(π) = n ℓ(π)` with `n = k + 1`
  (`Langlands.BushnellKutzko.SupercuspidalSwanLevelStatement`).

Then the supercuspidal twist Swan bound holds
(`Langlands.Henniart.SupercuspidalTwistSwanBoundStatement`): for every prime `p`, every
`K : PadicField.{uK} p`, every `k : ℕ`, every `χ : QuasiCharacter K` and every
supercuspidal class `π` of `GL_n(K)`, `n = k + 1`, with
`HasSupercuspidalSwan K π s`, the twist `supercuspidalCharacterTwist K k χ π` has a Swan
exponent `s'` with `s' ≤ max(s, n · sw(χ))`, and `s' = max(s, n · sw(χ))` when
`s ≠ n · sw(χ)`. Here `sw(χ)` is `Numerical.characterSwanExponent K χ`.

The four propositions are used exactly as published, by their Lean names; none is restated or
weakened here. L1 of the same family is not a hypothesis.

## Universe levels

All four propositions have the two universe parameters `uK` (the field
`PadicField.{uK} p`) and `uV` (the carriers of the representations: the second parameter of
`SmoothDualClass.{0, uK, uV}` in L0 and L2, and of
`SupercuspidalAutomorphicClass.{uK, uV}` in T2 and in the conclusion). Each is instantiated
at `.{uK, uV}` in that order, which is the order of its declared level parameters, so all
hypotheses and the conclusion concern the same field universe and the same carrier universe.
No other universe parameter occurs, so no further instantiation is needed.

## Provenance

This is an internal result: the last step of the proof of Lemma `lem:level`(ii) in the
operator's route note *The numerical local Langlands correspondence for GL_n: counts on the
two sides and the recommended route of proof* (`operator-numerical-llc-route-2026-11-16`,
`numerical-LLC-route.tex`). Lemma `lem:level` (lines 621–629) states in (ii) that
`ℓ(χπ) ≤ max(ℓ(π), k)`, with equality if `ℓ(π) ≠ k`, where `k = sw(χ)` (this is L2), and
"Hence, for `π ∈ A⁰_K(n)`: `sw(χπ) ≤ max(sw(π), n sw(χ))`, with equality if
`sw(π) ≠ n sw(χ)`" (this is the conclusion). The proof (lines 630–642) ends with "The statement
about Swan conductors follows from (i), since `χπ` is supercuspidal as well" (line 641): the
identity `sw(π) = n ℓ(π)` of Lemma `lem:level`(i), second sentence, which rests on
Proposition `prop:T2` (line 510) and is formalized as T2. The note defines `ℓ(π)` as a
minimum (lines 617–620); L0 states that this minimum exists. The proposition above records
exactly this deduction: the existence of the levels, their twist behaviour, and the
conversion between levels and Swan exponents for supercuspidals give the Swan bound.

## Remarks

- The implication is meant to be proved without further hypotheses. Its proof uses
  `characterSwanExponent K χ = multiplicativeConductor χ − 1`, which is the `k` of L2 by
  definition, and the Library's `GeneralLinear.SupercuspidalClass.toSmoothDualClass_twist`,
  which identifies the image of the supercuspidal twist with the twist
  `SmoothDualClass.twist (χ ∘ det)` used in L2. Multiplying L2's inequality by
  `n = k + 1 > 0` and converting with T2 gives the bound; `ℓ(π) ≠ sw(χ)` holds exactly when
  `sw(π) ≠ n · sw(χ)`.
- Rank one gives a sanity check: for `n = 1` the conclusion reads
  `sw(χχ₀) ≤ max(sw(χ₀), sw(χ))`, with equality when the two differ.
