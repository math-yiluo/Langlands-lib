# Unramified twists of pair factors

Author: Worker 11. This module, in namespace `Langlands.RankinSelberg`, states
how the L-factor and the epsilon factor of a pair change when one member is
twisted by the unramified character `|det|^u`, `u ∈ ℂ`: both are shifted from
`s` to `s + u`. The epsilon statement is from Henniart, *Caractérisation de la
correspondance de Langlands locale par les facteurs ε de paires*, Invent.
Math. 113 (1993), 339-350. The L statement is derived from the Rankin-Selberg
integrals of Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg
Convolutions*, Amer. J. Math. 105 (1983), 367-464. The factors are the
relations `IsPadicSymmetricLPolynomial` and `IsPadicSymmetricEpsilonFactor` of
the module `PadicPairFactors`, which cover both rank orders. The module
defines three statements, none of them proved.

## Source

- **Henniart 1993, §4.4, printed page 349** (registered as
  `henniart-1993-epsilon-pairs`; printed page = 0-based PDF page index + 339,
  read from the text layer). In the proof of Theorem 1.2, `π` is an
  irreducible supercuspidal representation of `G_n = GL_n(F)` and `π_ρ` one of
  `G_r`, `1 ≤ r ≤ n - 1`. Henniart writes that the needed equality follows from
  identities that are "conséquences des propriétés élémentaires des facteurs ε
  (cf. [De, §5] et [JPS 2])":
  `ε(π × π_ρ |·|^u, s, ψ) = ε(π × (π_ρ ⊗ (|·|^u ∘ det)), s, ψ) = ε(π × π_ρ, s + u, ψ)`,
  "pour tous nombres complexes s et u". Here `[JPS 2]` is the 1979 Comptes
  Rendus note *Facteurs L et ε du groupe linéaire*, which is not in the
  project literature, and `[De]` is Deligne's 1973 article on local constants
  (the Galois side).
- **JPSS 1983, (2.4), printed page 387** (registered as
  `jpss-1983-rankin-selberg`; read from the scan). For `W ∈ 𝒲(π; ψ)` on `G_r`
  and `W' ∈ 𝒲(σ; ψ̄)` on `G_t`: display (1), for `r = t`,
  `Ψ(s, W, W'; Φ) = ∫ W(g) W'(g) Φ(η_r g) |det g|^s dg` over `N_r\G_r`;
  display (2), for `r = t + 1`,
  `Ψ(s, W, W') = ∫ W(diag(g, 1)) W'(g) |det g|^(s-1/2) dg` over `N_t\G_t`;
  display (3), for `1 ≤ t ≤ r - 1` and `0 ≤ j ≤ r - t - 1`, `k = r - t - 1 - j`,
  `Ψ(s, W, W'; j) = ∫∫ W([g, 0, 0; x, 1_j, 0; 0, 0, 1_(k+1)]) W'(g) |det g|^(s-(r-t)/2) dx dg`.
- **JPSS 1983, Theorem (2.7), printed pages 390-391.** L is the normalized
  generator of the ideal spanned by the integrals (ii), and `ε(s, π × π', ψ)`,
  of the form `c q^(-ns)`, is defined by the functional equations (iii)(1)
  and (2). Their dual side uses the integrals of `W̃`, `W̃'`, functions of the
  pair `(π^ι, (π')^ι)` with `π^ι(g) = π(ᵗg⁻¹)`, at `1 - s`, divided by
  `L(1 - s, π^ι × (π')^ι)`, and the sign `ω_(π')(-1)^(r-1)`, where `π'` is the
  member of rank `t ≤ r`.
- **JPSS 1983, (2.12), printed page 403**: a pair is read with the larger rank
  first. This is the convention of the symmetric relations used here.

## Definitions

Throughout, `F : PadicField p` carries its canonical topological data, `q` is
its residue cardinality `F.canonicalTopologicalData.residueCardinality`, `ψ`
is a `UnitaryAdditiveCharacter` of `F`, and `ν` is in the published
`LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`.
Representations are actual representations `π` of `GL_(r+1)(F)` on a complex
vector space in universe `uV` and `σ` of `GL_(t+1)(F)` on one in universe
`uW`, for all `r` and `t`, in either rank order. `u` is a complex number and
`χ : Fˣ →* ℂˣ` a homomorphism with `χ(x) = |x|^u` for every `x`, where `|x|`
is the published normalized absolute value
`F.canonicalTopologicalData.normalizedAbs`, cast to `ℂ`, and the power is the
complex power. `σ ⊗ |det|^u` is the published
`Langlands.twist (χ.comp determinant) σ`, the action `g ↦ χ(det g) σ(g)` on the
same space, and `π ⊗ |det|^u` likewise.

The relations come from `PadicPairFactors`.
`IsPadicSymmetricLPolynomial F ψ ν π σ P` says `L(s, π × σ) = 1/P(q^(-s))`:
when `t ≤ r` it is `IsPadicPairLPolynomial` for `(π, σ)`, and when `r < t` it
is that relation for `(σ, π)`. That relation requires a compatible quotient
measure and asks, for every one, that `P` be the normalized generator of the
JPSS zeta values. `IsPadicSymmetricEpsilonFactor F ψ ν π σ e`, `e = (c, m)`,
says `ε(s, π × σ, ψ) = c q^(-ms)` in the same rank convention; it requires
nonzero Whittaker functionals (for `ψ` on the larger-rank member, for `ψ⁻¹` on
the smaller) and the functional equation with this monomial for every
compatible quotient measure and every pair of nonzero functionals.

`UnramifiedTwistLFactorStatement`: for all `p`, `F`, `ψ`, `ν`, `r`, `t`, `π`,
`σ`, `u` and `χ` as above, and every `P : ℂ[X]` with
`IsPadicSymmetricLPolynomial F ψ ν.val π σ P`, the polynomial
`P.comp (C (q^(-u)) * X)`, i.e. `X ↦ P(q^(-u) X)`, satisfies both
`IsPadicSymmetricLPolynomial F ψ ν.val π (σ ⊗ |det|^u)` and
`IsPadicSymmetricLPolynomial F ψ ν.val (π ⊗ |det|^u) σ`. Since
`P(q^(-u) q^(-s)) = P(q^(-(s+u)))`, this says
`L(s, π × (σ ⊗ |det|^u)) = L(s, (π ⊗ |det|^u) × σ) = L(s + u, π × σ)`.

`UnramifiedTwistEpsilonStatement`: for the same data and every `e : ℂˣ × ℤ`
with `IsPadicSymmetricEpsilonFactor F ψ ν.val π σ e`, there is `e' : ℂˣ × ℤ`
with `e'.2 = e.2`, `e'.1 = e.1 · q^(-(e.2 · u))`, and both
`IsPadicSymmetricEpsilonFactor F ψ ν.val π (σ ⊗ |det|^u) e'` and
`IsPadicSymmetricEpsilonFactor F ψ ν.val (π ⊗ |det|^u) σ e'`. With
`e = (c, m)`, `c q^(-mu) q^(-ms) = c q^(-m(s+u))`, so this says
`ε(s, π × (σ ⊗ |det|^u), ψ) = ε(s, (π ⊗ |det|^u) × σ, ψ) = ε(s + u, π × σ, ψ)`.
The existential only packages the unit `c q^(-mu)`; its value is fixed by the
formula.

`UnramifiedTwistStatement` is the conjunction of the two statements.

## Interpretation

- **Henniart's identity.** The epsilon statement is Henniart's display with
  `π_ρ |·|^u` read as `π_ρ ⊗ (|·|^u ∘ det)`, which is his first equality. His
  context has supercuspidal `π` and `π_ρ` with `π_ρ` of smaller rank, but the
  identity is a consequence of elementary properties of the factors and holds
  for every pair for which the factors are defined. The statement has no
  hypothesis beyond the factor relation of the untwisted pair; the relation
  itself carries nonzero Whittaker functionals and a compatible measure.
- **Derived parts.** Henniart twists the smaller-rank member. Twisting the
  larger-rank member, and the L-factor statement, are derived, not quoted. In
  the integrals (2.4)(1)-(3), the Whittaker functions of `σ ⊗ |det|^u` are the
  functions `g ↦ |det g|^u W'(g)` (the Library's
  `mem_inverseWhittakerSet_twist_iff` of `TwistInvariance`), and those of
  `π ⊗ |det|^u` are `g ↦ |det g|^u W(g)`. The block matrix in (2) and (3) has
  determinant `det g` (the Library's `determinant_unequalRankMatrix`). So in
  every case the integrand acquires the factor `|det g|^u`, and each integral
  of the twisted pair at `s` is the corresponding integral of the original
  pair at `s + u`. As functions of `X = q^(-s)` the zeta values of the twisted
  pair are the `R(q^(-u) X)` for `R` a zeta value of the original pair, so the
  normalized generator becomes `P(q^(-u) X)`; the normalization `P(0) = 1` is
  kept. On the dual side of the functional equation, `W̃(g) = W(w ᵗg⁻¹)` with
  `|det w| = 1`, so the dual functions of the twisted member acquire
  `|det g|^(-u)`, which shifts `1 - s` to `1 - s - u = 1 - (s + u)`. The sign
  is unchanged: the central character of the twisted member at `-1` gains the
  factor `|det(-1)|^u = 1`. Hence the gamma factor, the L-factors and the epsilon
  factor are all shifted by `u`.
- **Rank order.** The symmetric relations read the pair with the larger rank
  first. Since the statement twists either argument, it covers twisting the
  smaller-rank member (Henniart's case), the larger-rank member, and either
  member in equal rank, where the two arguments play different roles
  (Whittaker functionals for `ψ` and `ψ⁻¹`).
- **Unramified characters.** `χ(x) = |x|^u` determines `χ`. Every unramified
  quasicharacter of `Fˣ` has this form for some complex `u`, but that is not
  used; the statements are parametrized by `u`, as Henniart's is. The
  homomorphism `χ` is a separate argument, constrained by the displayed
  equation, because `Langlands.twist` takes a homomorphism into `ℂˣ`.
- **Measures.** `ν` self-dual for `ψ` is a hypothesis, as in the other JPSS
  units; JPSS use the self-dual measure for the Fourier transform in (2.7).
- **Field.** `F` is a p-adic field because the canonical topological data and
  the p-adic relations are published only for `PadicField`.
- **Not stated.** The gamma-factor shift, ramified twists (the Library's
  `TwistInvariance` treats the cancelling pair `π ⊗ χ`, `σ ⊗ χ⁻¹`, and
  `HighlyRamifiedStatement` treats highly ramified twists), and the dependence
  on `ψ`.

## Universes

`UnramifiedTwistLFactorStatement`, `UnramifiedTwistEpsilonStatement` and
`UnramifiedTwistStatement` have universe parameters `uF` (the field), `uV`
(the space of `π`) and `uW` (the space of `σ`).
