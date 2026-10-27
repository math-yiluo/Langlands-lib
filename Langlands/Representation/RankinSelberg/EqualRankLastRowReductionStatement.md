# Equal-rank integrals with a last-row orbit cutoff

This module defines only the proposition
`Langlands.RankinSelberg.EqualRankLastRowReductionStatement F T n`. It proves
nothing.

## Meaning of the Lean statement

Fix a prime `p`, a field `F : PadicField.{uF} p` and topological data
`T : F.TopologicalData`. The statement uses the topology, valuation and
local-field structure of `T`, and Borel σ-algebras on `GL_(n+1)`, `GL_(n+2)`,
their upper unipotent subgroups and the quotients `N_(n+1) \ GL_(n+1)`
(`LeftUnipotentQuotient n`) and `N_(n+2) \ GL_(n+2)`
(`LeftUnipotentQuotient (n+1)`). Here `GL_(n+2)` is written
`GeneralLinear (n + 1 + 1)`.

For every right-invariance instance of the two unipotent Haar measures
`unipotentHaar F.Carrier n` and `unipotentHaar F.Carrier (n + 1)`, every
measure `μ` on `N_(n+2) \ GL_(n+2)` that `IsCompatible` with
`generalLinearHaar F.Carrier (n + 1)` and `unipotentHaar F.Carrier (n + 1)`,
every measure `μ'` on `N_(n+1) \ GL_(n+1)` that `IsCompatible` with
`generalLinearHaar F.Carrier n` and `unipotentHaar F.Carrier n`, and every open
subgroup `J` of `GL_(n+2)` whose carrier is compact, there is a real `c > 0`
with the following property.

For every unitary additive character `ψ`, every
`W : WhittakerFunctions ψ (n + 1)` and `W' : InverseWhittakerFunctions ψ (n + 1)`
on `GL_(n+2)`, every `W'' : InverseWhittakerFunctions ψ n` on `GL_(n+1)`, and
every Schwartz–Bruhat function `Φ` on `F^(n+2)`, assume

1. `W(g j) = W(g)` and `W'(g j) = W'(g)` for all `g ∈ GL_(n+2)` and `j ∈ J`;
2. `W''(h) = W'(rankInclusion 1 h)` for all `h ∈ GL_(n+1)`, that is,
   `W''(h) = W'(diag(h, 1))`;
3. the function underlying `Φ` is exactly the indicator (value `1`, otherwise
   `0`) of the set `lastRow '' J = { e_(n+2) j : j ∈ J }`.

Then for every `s : ℂ`, with `abv = normalizedAbsoluteValue T`:

- `EqualRankConverges ψ abv μ W W' Φ s` holds if and only if
  `CorankOneConverges ψ abv μ' W W'' (s - 1/2)` holds; and
- `equalRankIntegral ψ abv μ W W' Φ s = c * corankOneIntegral ψ abv μ' W W'' (s - 1/2)`.

Unfolding the Library definitions in
`Langlands.Representation.RankinSelberg.QuotientIntegrals`, the left side is the
Bochner integral over `N_(n+2) \ GL_(n+2)` of
`W(g) W'(g) Φ(e_(n+2) g) |det g|^s`, and the right side is the Bochner integral
over `N_(n+1) \ GL_(n+1)` of
`W(diag(h,1)) W''(h) |det h|^((s - 1/2) - 1/2) = W(diag(h,1)) W'(diag(h,1)) |det h|^(s-1)`.
Both convergence predicates are Lebesgue integrability of these descended
integrands for the given measures. The constant `c` depends only on the two
quotient measures and on `J`; it is chosen before `ψ`, the functions and `s`.

The functions `W, W', W''` are arbitrary elements of the Library's Whittaker
function spaces; they need not come from a representation, and no central
character or `K`-finiteness is assumed. The only link between them is
right `J`-invariance and the restriction hypothesis 2.

## Source and derivation

The statement is derived from Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions* (1983), printed page 449 (PDF page 84),
displays (1) and (3). Display (1) decomposes the integral over `N_r \ G_r` as an
integral over `N_(r-1) \ G_(r-1) × Z_r × K_r` of `F(diag(g,1) z k) |det g|^(-1)`;
display (3) applies it to the equal-rank integral, giving an inner integral of
`W W'(diag(g,1) k) |det g|^(s-1)` over `N_(r-1) \ G_(r-1)` times an integral of
`Φ(η_r a k)` over `F^×`.

The Library form specializes this to a Schwartz–Bruhat function that is the
indicator of the last-row orbit of a compact open subgroup `J`, with `W, W'`
right `J`-invariant. Then `Φ(e_(n+2) g) ≠ 0` exactly when `g ∈ P J`, where `P`
is the mirabolic subgroup of matrices with last row `e_(n+2)`, and the
`K`- and central integrations collapse to a positive constant. The source fixes
unnamed Haar measures; the Library statement instead allows arbitrary
compatible quotient measures `μ, μ'` and records the normalization only as the
existence of a positive constant `c`. The `s - 1/2` shift is the Library's
convention for `corankOneIntegral`, which already contains the weight
`|det h|^(s - 1/2)`. The statement does not identify `c` and asserts no other
measure identity. Provenance: derived.

## Intended proof route (not part of the statement)

Write `ι(h) = diag(h, 1)`, `Y = { y(v) = [[I, v], [0, 1]] }`, so that
`P = ι(GL_(n+1)) ⋉ Y` and `N_(n+2) = ι(N_(n+1)) ⋉ Y`. Let `A` be the image of
`P ∩ J` in `GL_(n+1)`. The descended integrand is right `J`-invariant, and the
`N_(n+2)`-classes in `P J` are the disjoint double cosets `N ι(h) J`, which
correspond to the classes `N_(n+1) h A`. The equal-rank function restricted to
`ι(h)` is right `A`-invariant, because the characters of `W` and `W'` cancel on
the `Y`-components. A Weil-formula computation with the indicator of `g J`
gives `μ(N \ N ι(h) J) = vol(J) / vol_N(N ∩ ι(h) J ι(h)^(-1))`, and
`vol_N(N ∩ ι(h) J ι(h)^(-1)) = vol(N_(n+1) ∩ h A h^(-1)) · |det h| · vol(Y₀)`
with `Y₀ = { v : y(v) ∈ J }`. Hence each orbit carries `|det h|^(-1)` times a
constant multiple of its `μ'`-mass, which yields both the convergence
equivalence and the identity with
`c = vol(J) / (vol(Y₀) · vol(A))` for the corresponding Haar normalizations.

## Use

This is the analytic comparison needed by the equal-rank endpoint
`Langlands.RankinSelberg.EqualRankRankOneExtensionLDivisibilityStatement`
(task `82ed7f4d-388e-471f-8c3c-0f52ae4c1b28`). It replaces the strict-rank
JPSS Lemma 5.5 argument, which does not apply when the test and induced ranks
coincide.
