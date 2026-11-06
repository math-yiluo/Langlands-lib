# A supercuspidal pair partner with a pole at `s = 0`

Author: Worker 1719.
This module, in namespace `Langlands.RankinSelberg`, defines one statement,
`TemperedTwistSupercuspidalPoleStatement`. It is not proved here.

## Statement

Let `F` be a `p`-adic field with its canonical topological data, `ψ` a
`UnitaryAdditiveCharacter` of `F` and `ν` a self-dual Haar measure for `ψ`
(the published `LocalFactor.PadicAbelian.SelfDualHaar`). Let `k ≥ 1`, let `τ`
be a smooth representation of `GL_k(F)` that is irreducible (Mathlib's
`Representation.IsIrreducible`) and tempered (the published
`TopologicalData.IsTempered`: admissible, with a unitary central character and
matrix coefficients in `L^(2+ε)` modulo the center for every `ε > 0`), and let
`u` be a real number.

Then there are `r : ℕ`, a smooth representation `ρ` of `GL_(r+1)(F)` and a
polynomial `P : ℂ[X]` such that

- `ρ` is irreducible and supercuspidal (the published
  `GeneralLinear.IsSupercuspidal`);
- `r + 1 ≤ k`, and `r + 1 < k` whenever `τ` is not supercuspidal;
- `P` is the L-polynomial of the pair `(ν^u τ, ρ)`:
  `IsPadicRankLPolynomial F ψ ν (ν^u τ) ρ P`, that is
  `L(s, ν^u τ × ρ) = 1 / P(q^(-s))` (here the rank of `ν^u τ` is at least that
  of `ρ`, so this is `IsPadicPairLPolynomial` with `ν^u τ` first, JPSS's
  convention);
- `P(1) = 0`, i.e. `L(s, ν^u τ × ρ)` has a pole at `s = 0`.

Here `ν^u τ` is the published `TopologicalData.segmentFactor τ u`, the twist of
`τ` by `|det|^u`. The representation `τ` lives in an arbitrary universe `uV`;
`ρ` is produced in an arbitrary universe `uW`.

## Provenance

The statement is derived; it is the step of the proof of Henniart's
Théorème 1.6(b), (ii) ⇒ (i), that produces a pole from one block of a Langlands
datum. It is not stated as such in the sources; it combines the following.

- Henniart, *Une caractérisation de la correspondance de Langlands locale pour
  GL(n)*, Bull. SMF 130 (2002) (registered source
  `henniart-2002-characterization`; printed page = PDF page + 586):
  Théorème 1.6(b), printed pages 590-591; §3.2, printed page 597, the argument
  for part (a) that §3.3, printed page 598, transfers to part (b); §2.6,
  printed page 595: `L(s, St_n(ρ) × St_n'(ρ')) = ∏_j L(s, ν^(n+n'-1-j) ρ × ρ')`,
  `j = 1, …, inf(n, n')`, where `St_n(ρ)` is the essentially square-integrable
  quotient of `i(ρ, νρ, …, ν^(n-1) ρ)`; §2.8, printed page 596: the L-factor of
  a pair is the product of the L-factors of the essentially square-integrable
  pieces; §3.3, printed page 598, restating JPSS (8.1): for supercuspidal
  `π, π'` of equal rank, `L(s, π × π')` has a simple pole at `s = -α` when
  `π ≃ ν^α π'^∨`.
- Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg convolutions*,
  Amer. J. Math. 105 (1983) (registered source `jpss-1983-rankin-selberg`):
  (8.1)(ii), printed page 443; Theorem (8.2), printed pages 443-445;
  Proposition (8.4), printed pages 451-452.

Derivation (not formalized here). By the classification of tempered
representations, `τ` is irreducibly induced from essentially square-integrable
`St_(d_i)(ρ_i)` with unitary central characters, and `k = Σ d_i n(ρ_i)`.
Pick one of them, `St_d(ρ_0)` with `ρ_0` supercuspidal of rank `a`. Put
`ρ = (ν^(u+d-1) ρ_0)^∨`, irreducible supercuspidal of rank `a ≤ d a ≤ k`. By
Henniart §2.6 (JPSS (8.2)), `L(s, ν^u St_d(ρ_0) × ρ) = L(s, ν^(u+d-1) ρ_0 × ρ)`,
which has a simple pole at `s = 0` by JPSS (8.1)(ii). By Henniart §2.8 (JPSS
(8.4)), `L(s, ν^u τ × ρ)` is the product of the factors `L(s, ν^u St_(d_i)(ρ_i)
× ρ)`, each the reciprocal of a polynomial in `q^(-s)` with constant term `1`,
so the pole persists: `P(1) = 0`. Finally `a = k` forces a single piece with
`d = 1`, i.e. `τ = ρ_0` supercuspidal; so `a < k` when `τ` is not supercuspidal.
