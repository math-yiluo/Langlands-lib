# L0: every irreducible admissible representation of `GL_n(K)` has a normalized level

Module `Langlands.BushnellKutzko.NormalizedLevelExistenceStatement`, namespace
`Langlands.BushnellKutzko`. Uses `normalizedLevelValues` and `IsNormalizedLevel` from
`Langlands.BushnellKutzko.NormalizedLevel`.

Sources: C. J. Bushnell, *Hereditary orders, Gauss sums and supercuspidal representations of
GL_N* (1987), `bushnell-1987-hereditary-orders-gauss-sums`, (3.3), printed p. 196 (PDF p. 13);
operator route note `operator-numerical-llc-route-2026-11-16`, §4.4, definition of `ℓ(π)`
before Lemma `lem:level`, printed p. 15 ("`ℓ(π) = min {m / e(𝔄) : ...}`", which presupposes that the minimum
exists).

`NormalizedLevelExistenceStatement.{uK, uV} : Prop` is a statement; `normalizedLevelExistence`
(module `Langlands.BushnellKutzko.NormalizedLevelExistenceProof`) proves it.

## Statement

For every prime `p`, every `K : PadicField.{uK} p` (with the Library's canonical topology on
`K.Carrier` and on `GeneralLinear n K.Carrier`), every `n : ℕ` with `1 ≤ n`, and every class
`a : SmoothDualClass.{0, uK, uV} (k := ℂ) (G := GeneralLinear n K.Carrier)` of irreducible
admissible complex representations of `GL_n(K)`, there is `x : ℚ` with
`IsNormalizedLevel K n a x`, i.e. `x` is the least element of `normalizedLevelValues K n a`.

No other hypothesis is made.

## Why it holds

- Nonempty: a nonzero vector of a smooth representation is fixed by an open subgroup, which
  contains the congruence subgroup `U^{m+1}(𝔄(𝓛₀))` for the standard chain `𝓛₀ = (𝔭^i 𝔬^n)_i`
  and some `m`.
- A least element exists: every value is `m / e(𝓛)` with `1 ≤ e(𝓛) ≤ n`, so every value lies in
  `(1/n!) ℕ`, a discrete subset of `ℚ_{≥0}`; a nonempty subset of it has a least element.
