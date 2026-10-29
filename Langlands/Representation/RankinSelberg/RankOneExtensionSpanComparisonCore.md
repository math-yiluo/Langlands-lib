# Measure-theoretic core of the rank-one extension comparison

Module `Langlands.Representation.RankinSelberg.RankOneExtensionSpanComparisonCore`.

This helper module isolates the change of variables in the rank-one extension comparison. It
is used to prove `RankOneExtensionSpanComparisonStatement`. The main theorem,
`rankOneExtensionUnfoldingCore`, contains no representation theory. Its hypotheses are stated
for an abstract continuous function `H` on `GL_(1+(t+1))(K)`.

Notation: `N_(t+1) = upperUnipotent (t + 1) K`; `B(g, x, a) = [g, 0; x, a]`
(`rankOneExtensionLowerBlock`); `u(y) = [I, y; 0, 1]` (`rankOneExtensionUpperCell`);
`B(1, x, h)` (`rankOneExtensionLowerCell`) with `h ∈ B⁻_1 = lowerTriangularSubgroup 1 K`;
`χ(h)` means `χ (lowerScalarEntry h)`; `ν^(t+1) = Measure.pi fun _ => ν`.

## Provenance

Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg convolutions*, Amer. J. Math. 105 (1983),
Lemma 5.5 (printed pp. 424–426), compares an integral over `N_(t+2) \ GL_(t+2)` with an
integral over `N_(t+1) \ GL_(t+1) × M_(1×(t+1))`. It does so by integrating over the open
cell `N_(t+1) \ GL_(t+1) × M_(1×(t+1)) × K^× × K^(t+1)` and exchanging the lower block with
the upper cell. This module states that computation abstractly for this formalization. The
hypotheses `hH`, `hWc`, `hJ` and `htr` and the order of the integrals are not quoted from
the paper.

## Contents

Descent (`section Descent`), for any field `K`:

- `rankOneExtensionLowerBlock_mul_zero_one`: `B(m m', 0, 1) = B(m, 0, 1) B(m', 0, 1)`.
- `rankOneExtensionLowerBlock_zero_one_mul_lowerCell`:
  `B(g, 0, 1) B(1, x, h) = B(g, x, h)`.
- `rankOneExtensionCellDescent H hH` is the function `([g], z) ↦ H(B(g, 0, 1) z)` on
  `N_(t+1) \ GL_(t+1) × GL_(1+(t+1))`. It is well defined because of the hypothesis `hH`:
  `H(B(n, 0, 1) z) = H(z)` for `n ∈ N_(t+1)`. Its value on `([g], z)` is given by
  `rankOneExtensionCellDescent_mk`.

Topology (`section Topology`), for a topological ring `K`:

- `rankOneExtensionCellDescent_lowerBlock`: the descended function satisfies
  `Ψ(q, B(r, 0, 1) z) = Ψ(q r, z)`. This is the compatibility required by
  `integral_cellExchange_reorder` of
  [RankOneExtensionUnfoldingIntegral](RankOneExtensionUnfoldingIntegral.md).
- `continuous_rankOneExtensionLowerBlock_zero_one`: `g ↦ B(g, 0, 1)` is continuous.
- `continuous_rankOneExtensionCellDescent`: the descended function is continuous if `H` is.

Scaling (`section Scaling`):

- `integral_generalLinear_mulVec`. Let `ν` be a σ-finite additively left-invariant measure
  on `K` such that `x ↦ a x` sends `ν` to `χ(a)⁻¹ • ν` for `a ≠ 0`. Then for
  `g ∈ GL_(t+1)(K)` and strongly measurable `f`, `y ↦ f(g y)` is integrable for `ν^(t+1)`
  if and only if `f` is, and `∫ f(g y) dy = χ(det g)⁻¹ ∫ f(y) dy`.

Core (`section Core`): `rankOneExtensionUnfoldingCore`, for a second-countable T1 topological
field `K` with Borel σ-algebras on `K` and on the groups and quotient involved. The data are:

- `μ` on `N_(t+1) \ GL_(t+1)`, s-finite and invariant under all right translations;
- `dx` on `M_(1×(t+1))` and a right-invariant `ρ` on `B⁻_1`, both s-finite;
- `ν` on `K`, σ-finite, without atoms and additively left-invariant, with a measurable
  `χ : K →*₀ ℝ≥0` such that `x ↦ a x` sends `ν` to `χ(a)⁻¹ • ν` for `a ≠ 0`;
- a measurable density `D` on `N_(t+1) \ GL_(t+1)` with `D([g]) = χ(det g)⁻¹`;
- a measure `μ₂` on a space `Q₂`, a map `chart` from
  `N_(t+1) \ GL_(t+1) × (M_(1×(t+1)) × B⁻_1)` to `Q₂`, a constant `C`, and a function
  `fQ : Q₂ → ℂ`;
- a continuous `H : GL_(1+(t+1))(K) → ℂ`, an integrable `fB` on
  `(N_(t+1) \ GL_(t+1) × M_(1×(t+1)), μ × dx)`, an integrable `φ` on `(K^(t+1), ν^(t+1))`,
  and a measurable set `U ⊆ B⁻_1` with `ρ(U) < ∞` and `χ(h) = 1` for `h ∈ U`.

The hypotheses are:

- `htr` (chart transfer): if `fQ ∘ chart` is integrable for
  `P = (μ.withDensity D) × (dx × ρ)`, then `fQ` is integrable for `μ₂` and
  `∫ fQ dμ₂ = C ∫ fQ(chart p) dP(p)`;
- `hH`: `H(B(n, 0, 1) z) = H(z)` for `n ∈ N_(t+1)`;
- `hWc` (product formula on the cells):
  `H(B(g, x, h) u(y)) = 1_U(h) fB([g], x) φ(y)`;
- `hJ` (the integrand on `Q₂`): whenever `y ↦ H(u(y) B(g, x, h))` is integrable for
  `ν^(t+1)`, `fQ(chart([g], (x, h))) = ∫ H(u(y) B(g, x, h)) dy`.

The conclusion is that `fQ` is integrable for `μ₂` and

`∫ fQ dμ₂ = C · ρ(U) · (∫ φ dν^(t+1)) · ∫ fB d(μ × dx)`.

## Proof method

Let `Ψ = rankOneExtensionCellDescent H hH`; it is continuous, hence strongly measurable,
because `GL_(1+(t+1))(K)` is second countable (`secondCountable_generalLinear`).
`integral_cellExchange_reorder` applied to `Ψ` shows that `Ψ(q, u(y) B(1, x, h))` and
`χ(h)^(-(t+1)) Ψ(q, B(1, x, h) u(y))` have the same integrability and the same integral on
`(μ × (dx × ρ)) × ν^(t+1)`. By `hWc` and `χ = 1` on `U`, the second function is
`fB(q, x) 1_U(h) φ(y)`. It is integrable with integral `(∫ fB) ρ(U) (∫ φ)`
(`Integrable.mul_prod`, `integral_prod_mul`, after reassociating the product measure with
`measurePreserving_prodAssoc`).

Fubini (`Integrable.prod_right_ae`, `Integrable.integral_prod_left`, `integral_prod`) then
gives, for almost every `p = ([g], (x, h))`, the integrability of `y ↦ Ψ(p.1, u(y) B(1, x, h))`.
The identity `B(g, 0, 1) u(y) = u(g y) B(g, 0, 1)` (`rankOneExtensionLowerBlock_upperCell`)
rewrites this function as `y ↦ H(u(g y) B(g, x, h))`. The scaling lemma
`integral_generalLinear_mulVec` and `hJ` identify its integral with
`χ(det g)⁻¹ fQ(chart p) = D([g]) fQ(chart p)`. The density `D` is finite everywhere, and
`P` is `(μ × (dx × ρ)).withDensity (D ∘ fst)` by `prod_withDensity_left`. Hence `fQ ∘ chart`
is integrable for `P` (`integrable_withDensity_iff_integrable_smul'`), and its integral is
the iterated integral above (`integral_withDensity_eq_integral_toReal_smul`). Finally `htr`
transfers integrability and the value to `μ₂`.
