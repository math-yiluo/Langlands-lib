# Deligne's modified constant `ε₀` in rank one

Worker 33 wrote this module for task `e534647a`. It adds the rank-one case of
Deligne's modified local constant `ε₀` to that task's coverage map. The main
declaration is `Langlands.LocalFactor.PadicAbelianEpsilonZeroStatement`. It is
a proposition only. Nothing is assumed as an axiom and nothing is proved. The
module defines `ε₀` of a quasicharacter from the published fixed-Haar epsilon
expression (Deligne (3.4.3.3)) and states Deligne's (3.4.3.4) and (3.4.3.5)
for it.

## Objects

Everything except `ε₀` comes from the published companion
`Langlands.LocalFactor.Abelian.Padic` (`PadicAbelianStatement` uses the same
objects):

- a p-adic field `F` with its `TopologicalData` `T`. Write `ord` for the
  normalized valuation, `O` for the integer ring, `U = integralUnits T` for its
  elements of order zero, and `q = T.residueCardinality` for the residue
  cardinality.
- quasicharacters `χ` of `F^×` (`HarmonicAnalysis.Quasicharacter`), unitary
  additive characters `ψ`, and additive Haar measures `μ`.
- `ConductorAt T χ a`: `a` is the least level `b ≥ 0` such that `χ` is trivial
  on the unit group of level `b`. Level `0` is `U` and level `b > 0` is
  `1 + π^b O`. This `a` is Deligne's `a(χ)`, and `conductorAt_iff` identifies it
  with the constructed conductor `T.multiplicativeConductor χ`.
- `AdditiveConductorAt T ψ n`: `n` is the greatest integer such that `ψ` is
  trivial on `{x : ord x ≥ -n}`, that is on `π^(-n) O`. This is Deligne's and
  Tate's `n(ψ)`; `additiveConductorAt_iff` identifies it with
  `T.additiveConductor ψ`.
- `spectralVariable T s = exp(-s log q) = q^(-s)`.
- `gaussIntegrand T χ ψ s x = χ(x)^(-1) · |x|^(-s) · ψ(x)` for `x ≠ 0`, with
  `|x|` the normalized absolute value. This is the integrand of
  `(χ ω_s)^(-1) ψ`, where `ω_s = |·|^s`.
- `epsilonAt T π χ ψ μ a n s`, the fixed-Haar epsilon `ε(χ ω_s, ψ, μ)` at the
  conductor levels `a` and `n` and the uniformizer `π`:
  - if `a = 0`, it is `χ(π)^n · q^(n(1-s)) · μ(O)`;
  - if `a > 0`, it is the integral of `gaussIntegrand` over the shell
    `{x : ord x = -(n + a)}`.

## Definitions

Both definitions live in the namespace `Langlands.LocalFactor.PadicAbelian`.

- `epsilonZeroAt T π χ ψ μ a n s` is `ε₀(χ ω_s, ψ, μ)` at the conductor levels
  `a`, `n` and the uniformizer `π`:
  - if `a = 0`, it is `-(χ(π) · q^(-s)) · epsilonAt T π χ ψ μ a n s`;
  - if `a > 0`, it is `epsilonAt T π χ ψ μ a n s`.
- `epsilonZero T χ ψ μ s` is `epsilonZeroAt` at the constructed conductors
  `T.multiplicativeConductor χ`, `T.additiveConductor ψ` and the Library's
  uniformizer `uniformizerUnit T`. It mirrors the published constructor
  `PadicAbelian.epsilon`. The statement below is phrased with
  `epsilonZeroAt` at every level satisfying `ConductorAt` and
  `AdditiveConductorAt`, which by `conductorAt_iff` and
  `additiveConductorAt_iff` covers `epsilonZero`.

This is Deligne (3.4.3.3): `ε(χ, ψ, dx) = ε₀(χ, ψ, dx)` if `χ` is ramified and
`ε(χ, ψ, dx) = ε₀(χ, ψ, dx) · (-χ(π))^(-1)` if `χ` is unramified. It is the
rank-one case of Deligne (5.1), `ε₀ = ε · det(-F | V^I)`, because a geometric
Frobenius acts on an unramified character by `χ(π)`. The definition applies
(3.4.3.3) to `χ ω_s`. This quasicharacter has the same conductor as `χ` and
`(χ ω_s)(π) = χ(π) |π|^s = χ(π) q^(-s)`, which gives the factor in the
case `a = 0`. At `s = 0`, `epsilonZeroAt` is `ε₀(χ, ψ, μ)` itself.

## The statement

`PadicAbelianEpsilonZeroStatement` says the following. Let `p` be a prime,
`F` a p-adic field with topological data `T`, and use the Borel measurable
structure of `T`'s topology. Let `π` be any element of `F^×` with
`ord π = 1`. Let `χ` be a quasicharacter with `ConductorAt T χ a`, `μ` an
additive Haar measure, and `ψ` a unitary additive character with
`AdditiveConductorAt T ψ n`. Write `ε₀(χ, s)` for
`epsilonZeroAt T π χ ψ μ a n s`, and put

`N = n + (a - 1) + 1`, with `a - 1` truncated at `0`.

Deligne writes this exponent `n(ψ) + sw(χ) + 1`. His Swan conductor `sw(χ)` is
`0` if `a ≤ 1` and `a - 1` if `a ≥ 1`, which is the truncated `a - 1`. So
`N = n + 1` for `a = 0` and `N = n + a` for `a > 0`. Then four clauses hold:

1. (Deligne (3.4.3.4)) For every `c ∈ F^×` with `ord c = N` and every
   `s ∈ ℂ`, `ε₀(χ, s)` is the integral of `gaussIntegrand T χ ψ s` over
   `c^(-1) U` with respect to `μ`. That is,
   `ε₀(χ ω_s, ψ, μ) = ∫_{c^(-1) U} (χ ω_s)^(-1)(x) ψ(x) dμ(x)`.
2. (Deligne (3.4.3.5), first formula) For every unramified quasicharacter
   `ω` (`ConductorAt T ω 0`) and every `s`,
   `ε₀(χ ω, s) = ω(π)^N · ε₀(χ, s)`. The left side uses the same level `a`,
   which is also the conductor of `χ ω` because `ω` is trivial on `U`.
3. (Spectral form) For every `s`, `ε₀(χ, s) = ε₀(χ, 0) · q^(-N s)`, with
   `q^(-N s) = exp(-N s log q)`.
4. (Independence of the uniformizer) For every `ρ ∈ F^×` with `ord ρ = 1` and
   every `s`, `epsilonZeroAt` at `ρ` equals `epsilonZeroAt` at `π`.

### Design choices

- **Spectral variable.** Deligne states (3.4.3.4) and (3.4.3.5) for a
  quasicharacter `χ`. Every quasicharacter `χ ω_s` is again a quasicharacter
  with the same conductor, so stating the clauses for `χ ω_s` at every `s` is
  an instance of the same formulas. Clause 3 is the rank-one case of the second
  formula of Deligne (5.5.2), `ε₀(V, s) = ε₀(V) q^(-(sw(V) + dim V (n(ψ) + 1)) s)`;
  it is included because `epsilonZeroAt` is a function of `s`.
- **Explicit levels and uniformizer.** As in the published
  `PadicAbelianStatement`, the levels `a` and `n` are explicit with their
  characterizing predicates, and every uniformizer is allowed. Clause 4 shows
  that the value does not depend on the choice of uniformizer.
- **The integral in clause 1** is over the image of `U` under multiplication
  by `c^(-1)`. This is the shell `{x : ord x = -N}`, so the clause does not
  depend on the choice of `c`.
- **Only the first formula of (3.4.3.5).** Deligne's second formula there,
  `ε(χ ω) = ω(π^(n + a)) ε(χ)`, is about `ε`, not `ε₀`. It is the unramified
  twist clause of the published `PadicAbelianStatement`.

### Why the clauses hold

This is recorded only to explain the hypotheses and is not part of the
statement.

- Clause 1, `a > 0`: then `N = n + a` and `ε₀ = ε` is the integral over the
  shell `{ord x = -(n + a)}`, which is `c^(-1) U`.
- Clause 1, `a = 0`: then `N = n + 1`. On `{ord x = -(n + 1)}`,
  `χ^(-1)(x) = χ(π)^(n+1)` and `|x|^(-s) = q^(-(n+1)s)`. The integral of `ψ`
  over `π^(-(n+1)) O` is `0`, since `ψ` is nontrivial there by maximality of
  `n`. Its integral over `π^(-n) O` is `μ(π^(-n) O) = q^n μ(O)`. So the
  integral over the shell is
  `-χ(π)^(n+1) q^(-(n+1)s) q^n μ(O) = -χ(π) q^(-s) · χ(π)^n q^(n(1-s)) μ(O)`,
  which is `ε₀(χ, s)`.
- Clause 2: for `a > 0`, `ω^(-1)(x) = ω(π)^(n+a)` on the shell. For `a = 0`,
  `ε(χ ω) = ω(π)^n ε(χ)` and `-(χ ω)(π) = -χ(π) ω(π)` contributes one more
  factor `ω(π)`.
- Clause 3: on the shell of clause 1, `|x|^(-s) = q^(-N s)`.
- Clause 4: for `a > 0`, the value does not involve `π`. For `a = 0`, `χ` is
  trivial on `U`, so `χ(ρ) = χ(π)`.

### Not stated here

- The nonabelian `ε₀` and its laws (Deligne (5.1)–(5.6)). They concern a
  local-constant system rather than the rank-one Gauss integral.
- A comparison of `epsilonZeroAt` with the value of a nonabelian system on a
  character. This module does not state one.

## Sources

`deligne-1973-local-constants`, SHA-256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`:
P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*,
LNM 349 (1973). The PDF page is the printed page minus 500.

- §3.4, printed p.527 (PDF p.27): `n(ψ)`, the largest `n` with
  `ψ|π^(-n) O = 1`; the conductor `a(χ)`, `0` if `χ` is unramified and
  otherwise the least `m` with `χ|(1 + (π)^m) = 1`; the Swan conductor
  `sw(χ)`, `0` for `χ` unramified or tamely ramified and `a(χ) - 1` for `χ`
  ramified; and `γ`, an element of `K^*` of valuation `n(ψ) + sw(χ) + 1`.
- §3.4.3, printed p.528 (PDF p.28): (3.4.3.2), the Gauss integral
  `ε(χ, ψ, dx) = ∫_{γ^(-1) O^*} χ^(-1)(x) ψ(x) dx` for `χ` ramified;
  (3.4.3.3), `ε = ε₀` for `χ` ramified and
  `ε = ε₀ · (-χ(π))^(-1)` for `χ` unramified; (3.4.3.4),
  `ε₀(χ, ψ, dx) = ∫_{γ^(-1) O^*} χ^(-1)(x) ψ(x) dx` with
  `v(γ) = n(ψ) + sw(χ) + 1`; (3.4.3.5), for `ω` unramified,
  `ε₀(χ ω, ψ, dx) = ω(π^(n(ψ) + sw(χ) + 1)) ε₀(χ, ψ, dx)` and
  `ε(χ ω, ψ, dx) = ω(π^(n(ψ) + a(χ))) ε(χ, ψ, dx)`.
- §5.1 and (5.5.2), printed pp.548–549 (PDF pp.48–49): the general definition
  `ε = ε₀ det(-F, V^I)^(-1)` and the spectral form of `ε₀`, of which clause 3
  is the rank-one case.
