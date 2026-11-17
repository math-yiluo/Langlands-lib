# L1: a fundamental stratum in `π` computes its normalized level

Module `Langlands.BushnellKutzko.FundamentalStratumLevelStatement`, namespace
`Langlands.BushnellKutzko`. Uses `IsLevelOne`, `ContainsStratum` and `IsNormalizedLevel` from
`Langlands.BushnellKutzko.NormalizedLevel`, and `LatticeChain`, `endFiltration`, `period` from
the Library's `Langlands.BushnellKutzko.LatticeChain`.

Sources:

- C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups*
  (1993), `bushnell-kutzko-1993-admissible-dual-gln` (PDF page = printed page + 12):
  Introduction, printed p. 8 ("any two fundamental strata `[𝔄, n, n − 1, b]` occurring in the
  same irreducible representation `π` have the same normalised level `n / e(𝔄|𝔬_F)`"); §2.3,
  printed p. 57: definition of a fundamental stratum (`b + 𝔓^{1−n}` contains no nilpotent
  element of `A`) and (2.3.1) (a non-fundamental coset lies in a coset of smaller normalized
  level, = Bushnell 1987, Theorem 1).
- C. J. Bushnell, *Hereditary orders, Gauss sums and supercuspidal representations of GL_N*
  (1987), `bushnell-1987-hereditary-orders-gauss-sums` (PDF page = printed page − 183):
  Theorem 1, printed p. 192; Remark (2.9), printed p. 195; (3.3) and Theorem 2′, printed
  pp. 196–197 (an order minimizing `ℓ(𝔄, π) / e(𝔄)` carries a fundamental stratum of `π`).
- Operator route note `operator-numerical-llc-route-2026-11-16`, Lemma `lem:level`(i), first
  sentence (marked "[literature]"), printed pp. 15–16, with a short proof in the note.

`FundamentalStratumLevelStatement.{uK, uV} : Prop` is an unproved statement; a later
`lean.proof@1` task proves it.

## Statement

For every prime `p`, every `K : PadicField.{uK} p`, every `n ≥ 1`, every
`ψ : AddChar K.Carrier ℂ` with `IsLevelOne K ψ`, every class
`a : SmoothDualClass.{0, uK, uV} (k := ℂ) (G := GeneralLinear n K.Carrier)`, every lattice
chain `𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin n → K.Carrier)`, every `m : ℕ` and every
`b ∈ Module.End K.Carrier (Fin n → K.Carrier)`: if

1. `1 ≤ m`,
2. `b ∈ 𝔓^{-m}(𝓛)` (`𝓛.endFiltration (-(m : ℤ))`),
3. the stratum `[𝔄(𝓛), m, m − 1, b]` is **fundamental**, written out as: for every
   `y ∈ 𝔓^{1−m}(𝓛)` (`𝓛.endFiltration (1 - (m : ℤ))`), `b + y` is not nilpotent, and
4. `ContainsStratum K n ψ a 𝓛 m b` (`a` contains the stratum),

then `IsNormalizedLevel K n a (m / e(𝓛))`, where `e(𝓛) = 𝓛.period` and the quotient is taken in
`ℚ`.

The fundamental condition is stated directly from the Library's `𝔓^j`, because the
fundamental-strata definition of Task 7412 is not yet in the Library. It is BK93's definition
(printed p. 57) verbatim: `b + 𝔓^{1−m}` contains no nilpotent element of `A`.

## Relation to the sources

`IsNormalizedLevel K n a (m / e)` says two things: `a` has a nonzero vector fixed by
`U^{m+1}(𝔄(𝓛))` (true because `ψ_b` is trivial on `U^{m+1}`), and no lattice chain `𝓛'` and
`m'` with `m'/e(𝓛') < m/e(𝓛)` give a vector fixed by `U^{m'+1}(𝔄(𝓛'))`. The second part is
the uniqueness of the level of a fundamental stratum: BK93 Introduction p. 8 states it for two
fundamental strata; with Bushnell 1987 Theorem 2′ (the minimum of `ℓ(𝔄, π)/e(𝔄)` is the level of
a fundamental stratum, or `0`) it gives the minimum over all values. The route note's proof of
Lemma `lem:level`(i) argues directly against any `m'/e' < m/e`, including `m' = 0`.
