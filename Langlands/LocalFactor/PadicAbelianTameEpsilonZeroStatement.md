# Deligne's tame Gauss-sum formula for `ε₀`

Worker 33 wrote this module for task `e534647a`. It adds Deligne (5.10) to that
task's coverage map. This is the evaluation of the rank-one modified local
constant `ε₀` as a residue-field Gauss sum when the quasicharacter is at most
tamely ramified. The main declaration is
`Langlands.LocalFactor.PadicAbelianTameEpsilonZeroStatement`. It is a
proposition only. Nothing is assumed as an axiom and nothing is proved.

## Objects

The objects come from the published modules
`Langlands.LocalFactor.Abelian.Padic` and
`Langlands.LocalFactor.PadicAbelianEpsilonZeroStatement`:

- a p-adic field `F` with its `TopologicalData` `T`. Write `ord` for the
  normalized valuation, `O = T.Integers` for the integer ring of the actual
  valuation, `k = T.ResidueField` for its residue field,
  `T.residue : O → k` for the residue map, and `q = T.residueCardinality` for
  the cardinality of `k`. `PadicAbelian.integerRing T` is `O` as a subset of
  `F`.
- quasicharacters `χ` of `F^×`, unitary additive characters `ψ`, and additive
  Haar measures `μ`.
- `ConductorAt T χ a`: `a` is Deligne's conductor `a(χ)`. So `a = 0` means `χ`
  is trivial on the units `O^×`, and `a ≤ 1` means `χ` is trivial on
  `1 + πO`.
- `AdditiveConductorAt T ψ n`: `n` is Deligne's `n(ψ)`, the greatest integer
  such that `ψ` is trivial on `π^(-n) O`. So `n = -1` means `ψ` is trivial on
  the maximal ideal `πO` but not on `O`.
- `characterExtension T χ`, which is `χ` on `F^×` and `0` at `0`.
- `epsilonZeroAt T π χ ψ μ a n s`, the rank-one `ε₀(χ ω_s, ψ, μ)` at the
  conductor levels `a`, `n` and the uniformizer `π`, with `ω_s = |·|^s`
  (Deligne (3.4.3.3)).

## Definition

`PadicAbelian.residueGaussSum T χ ψ σ`, for a map
`σ : k^× → O`, is

`τ = -∑_{x ∈ k^×} χ(σ x)^(-1) · ψ(σ x)`.

Here `χ(σ x)^(-1)` means `(characterExtension T χ (σ x))^(-1)`. The sum is a
`finsum` over the finite group `k^×`. The Library proves that `k` is finite
(`TopologicalData.finite_residueField`), so this is the ordinary finite sum.

When `σ` is a section of the residue map (`T.residue (σ x) = x`), each `σ x`
is a unit of `O`. If moreover `a(χ) ≤ 1` and `ψ` is trivial on `πO`, then
`χ_k(x) = χ(σ x)` and `ψ_k(x) = ψ(σ x)` are Deligne's characters of `k^×` and
`k` defined by `χ` and `ψ`. They do not depend on the section. Then
`residueGaussSum` is Deligne's Gauss sum (5.10.2),
`τ(χ_k, ψ_k) = -∑_{x ∈ k^*} χ_k^(-1)(x) ψ_k(x)`. The definition itself accepts
any map `σ`. The statement below uses it only with sections and under these
hypotheses.

## The statement

`PadicAbelianTameEpsilonZeroStatement` says the following. Let `p` be a prime,
`F` a p-adic field with topological data `T`, and use the Borel measurable
structure of `T`'s topology. Let `π ∈ F^×` with `ord π = 1`. Let `χ` be a
quasicharacter with `ConductorAt T χ a` and `a ≤ 1`. Let `ψ` be a unitary
additive character with `AdditiveConductorAt T ψ (-1)`. Let `σ : k^× → O`
satisfy `T.residue (σ x) = x` for every `x ∈ k^×`. Write `τ` for
`residueGaussSum T χ ψ σ`. Then three clauses hold:

1. (Deligne (5.10.1)) For every additive Haar measure `μ` such that the ideal
   `(π) = π · O` has `μ`-measure `1`, and every `s ∈ ℂ`,
   `epsilonZeroAt T π χ ψ μ a (-1) s = -τ`.
   That is, `ε₀(χ ω_s, ψ, μ) = -τ(χ_k, ψ_k)`.
2. (Deligne, after (5.10.2): `τ` equals `1` for `χ_k` trivial) If `a = 0`,
   then `τ = 1`.
3. (Deligne (5.10.3)) For every additive Haar measure `μ` and every `s ∈ ℂ`,
   `epsilonZeroAt T π χ ψ μ a (-1) s · (epsilonZeroAt T π 1 ψ μ 0 (-1) s)^(-1) = τ`.
   The left side is `ε₀(χ ω_s, ψ, μ) / ε₀(ω_s, ψ, μ)`, the multiplicative
   extension of `ε₀` to the degree-zero virtual character `[χ ω_s] - [ω_s]`.
   Here `1` is the trivial quasicharacter, whose conductor is `0`.

### Design choices

- **Spectral variable.** Deligne states (5.10.1) for `χ`. For every `s`, the
  quasicharacter `χ ω_s` again has conductor `a ≤ 1`. It agrees with `χ` on
  `O^×`, so it has the same residue character `χ_k`. Stating clauses 1 and 3
  at every `s` is therefore an instance of Deligne's formulas.
- **Residue characters through a section.** The Library has no construction of
  the characters `χ_k` and `ψ_k`. The statement reads them through an
  arbitrary section `σ` of the actual residue map on `k^×`. It quantifies over
  every such section, so it also asserts that the sum does not depend on the
  section. Sections exist because the residue map is surjective.
- **Haar normalization.** Deligne's hypothesis `∫_(π) dx = 1` is written as
  `μ((fun v => π · v) '' O) = 1`. Clause 3 needs no normalization, because
  `ε₀` of a rank-one character is linear in `μ` (Deligne (5.3)), so the
  quotient does not depend on `μ`.
- **The virtual quotient.** Deligne writes (5.10.3) as `ε₀([χ] - [1], ψ)`.
  The Library has no `ε₀` of virtual rank-one characters. By additivity
  (Deligne (5.2)) it is the quotient `ε₀(χ) / ε₀(1)`, which clause 3 states
  directly. At `s`, the virtual character is `[χ ω_s] - [ω_s]`.
- **Explicit levels and uniformizer.** As in the published
  `PadicAbelianEpsilonZeroStatement`, the levels and the uniformizer are
  explicit, with their characterizing predicates. The level `a` of `χ` is the
  actual conductor by `conductorAt_iff`, and `-1` is the actual conductor of
  `ψ` by `additiveConductorAt_iff`.

### Why the clauses hold

This is recorded only to explain the hypotheses and is not part of the
statement. Write `vol = μ(πO)`, so `μ(O) = q · vol`.

- Clause 1, `a = 1`: by definition `ε₀ = ε` is the integral of
  `χ^(-1)(x) |x|^(-s) ψ(x)` over the shell `{ord x = 0} = O^×`. There
  `|x|^(-s) = 1`. The integrand is constant on each coset `σ x + πO`, because
  `χ` is trivial on `1 + πO` and `ψ` on `πO`. So the integral is
  `vol · ∑_x χ(σ x)^(-1) ψ(σ x) = -vol · τ`.
- Clause 1, `a = 0`: by definition
  `ε₀ = -χ(π) q^(-s) · χ(π)^(-1) q^(-(1-s)) μ(O) = -q^(-1) μ(O) = -vol`.
  Also `χ(σ x) = 1`, and `∑_{x ∈ k} ψ_k(x) = 0` because `ψ_k` is nontrivial.
  So `∑_{x ∈ k^×} ψ_k(x) = -1` and `-τ = -1`.
- Clause 2 is the last computation.
- Clause 3: by the two cases, `ε₀(χ ω_s) = -vol · τ` for every Haar measure,
  and `ε₀(ω_s) = -vol`.

### Not stated here

- Deligne's (5.11) (the global product formula) and his finite-field Gauss-sum
  identities (5.12)–(5.15). The latter are statements about finite fields, not
  local constants.
- A comparison of `epsilonZeroAt` with the value of a nonabelian system on a
  character.

## Sources

`deligne-1973-local-constants`, SHA-256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`:
P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*,
LNM 349 (1973). The PDF page is the printed page minus 500.

- §5.10, printed p.550 (PDF p.50): for `K` non-archimedean, `a(χ) ≤ 1`,
  `n(ψ) = -1` and `∫_(π) dx = 1`, with `χ_k` and `ψ_k` the characters of `k^*`
  and `k` defined by `χ` and `ψ`: (5.10.1) `ε₀(χ, ψ, dx) = -τ(χ_k, ψ_k)`;
  (5.10.2) `τ(χ_k, ψ_k) = -∑_{x ∈ k^*} χ_k^(-1)(x) ψ_k(x)`, equal to `1` for
  `χ_k` trivial; (5.10.3) `ε₀([χ] - [1], ψ) = τ(χ_k, ψ_k)`.
- §3.4, printed p.527 (PDF p.27): `n(ψ)` and the conductor `a(χ)`.
- §3.4.3, printed p.528 (PDF p.28): (3.4.3.3), the definition of the rank-one
  `ε₀` used by `epsilonZeroAt`.
- §5.2 and §5.3, printed p.548 (PDF p.48): additivity of `ε₀`, and its scaling
  in the Haar measure, used in the design notes on clause 3.
