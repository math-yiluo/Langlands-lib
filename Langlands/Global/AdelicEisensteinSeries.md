# Eisenstein series on actual adelic points

Module `Langlands.Global.AdelicEisensteinSeries` constructs the twist
`φ_λ(g) = φ(g) m_P(g)^λ` and the Eisenstein series
`E(g, φ, λ) = ∑_{γ ∈ P(F) \ G(F)} φ_λ(γ g)` for an actual parabolic subgroup
of an affine group scheme over a number field. It is a definition module and
proves nothing.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`. §2.1 (journal
p.190) defines `m_P : G(𝔸) → M(𝔸)/M(𝔸)^1` as the left `U(𝔸)`-invariant,
right `K`-invariant extension of the projection of `M(𝔸)`, and writes
`m_P(g)^λ` for `λ ∈ 𝔛_P`. §2.2 (p.191), formula (2.1), sets
`φ_λ(g) = φ(g) m_P(g)^λ` for `φ ∈ 𝒜_P` and
`E(g, φ, λ) = ∑_{γ ∈ P(F)\G(F)} φ_λ(γ g)`. Mœglin–Waldspurger II.1.5 (registered
as `moeglin-waldspurger-1995-spectral-decomposition`, chapter file
`06.1_pp_78_100_Definitions.pdf`, printed p.85) gives the same series.

## Existing objects used

- `IsIwasawaCompact p K` and its height `hK.height : G(𝔸) → Hom(X^*(P), ℝ)`
  (module `Langlands.Global.AdelicIwasawaHeight`): for a closed subgroup
  `p : P → G` and a compact `K` with `P(𝔸)K = G(𝔸)`, `H_P(p(q)k) = log_P(q)`.
  This is the source's `m_P` in additive form: `log_P` is the normalized
  `characterLog`, whose kernel is `P(𝔸)^1`, and the published
  `realCharacterDualMap_height_eq` identifies it with `log_M(m)` on
  `g = umk`.
- `ComplexCharacterParameter F P = ℂ ⊗[ℤ] X^*(P)` and
  `complexParameterPairing F P` (module `Langlands.Global.AdelicComplexParameters`),
  the source's `𝔛_P = X^*(M) ⊗ ℂ` (through `X^*(P) = X^*(M)`) and its pairing
  with `Hom(X^*(P), ℝ)`.
- `rationalSubgroup F G`, the image of `G(F)` in `G(𝔸)`, and `map F P G p`,
  the adelic point map of `p`.

## Definitions

Let `hK : IsIwasawaCompact p K`, `φ : G(𝔸) → ℂ`, `λ ∈ X^*(P) ⊗ ℂ`, `g ∈ G(𝔸)`.

- `hK.heightPower λ g = exp ⟨λ, H_P(g)⟩`, the source's `m_P(g)^λ`. For
  `λ = s ⊗ χ` it is `|χ(q)|^s` when `g = p(q) k`.
- `hK.parameterTwist φ λ g = φ(g) · m_P(g)^λ`, the source's `φ_λ(g)`.
- `parabolicRationalSubgroup F p` is the subgroup `P(F)` of the group
  `G(F) = rationalSubgroup F G`: the image of the principal points of `P`
  under `p`, as a subgroup of the rational points of `G`.
- `ParabolicRationalCosets F p` is the space of right cosets `P(F) γ`,
  `γ ∈ G(F)` (the quotient by `QuotientGroup.rightRel`), the source's
  `P(F) \ G(F)`.
- `hK.eisensteinTerm φ λ g c = φ_λ(γ_c g)`, where `γ_c ∈ G(F)` is the
  representative of the coset `c` chosen by `Quotient.out`.
- `hK.eisensteinSeries φ λ g = ∑' c, hK.eisensteinTerm φ λ g c`, the
  unconditional sum over `P(F) \ G(F)`.

## Conventions

For `φ ∈ 𝒜_P` the function `γ ↦ φ_λ(γ g)` is left `P(F)`-invariant: `φ` is
left invariant under `U(𝔸)M(F) ⊇ P(F)`, and `H_P` is invariant under
principal points of `P` (published `height_rational_mul`). The terms then do
not depend on the chosen representatives. This invariance is not proved here,
and the definition uses chosen representatives so that it needs no
hypothesis on `φ`.

The sum is Mathlib's `tsum` in `ℂ`. It is the value of the series where the
terms are summable, which in `ℂ` is the same as absolute convergence, and
`0` otherwise. The source asserts convergence only for `Re λ` sufficiently
regular in the positive chamber; that assertion is the separate statement
`Langlands.Global.EisensteinAbsoluteConvergenceStatement`. Values outside
the region of convergence are not the meromorphic continuation.

## Scope

No convergence, automorphy, holomorphy, continuation or functional equation
is asserted here. The parabolic `p` and the compact `K` are arbitrary inputs:
the standardness of `P` and the properties of `K` are hypotheses of the
statements that use these definitions.
