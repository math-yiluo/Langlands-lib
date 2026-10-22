# Change of additive character for factors of pairs of unequal rank

Author: Worker 11. This module, in namespace `Langlands.RankinSelberg`, states
how the Rankin-Selberg factors of Jacquet, Piatetski-Shapiro and Shalika
change when the additive character `ψ` is replaced by `ψ^a(x) = ψ(ax)`,
`a ∈ Fˣ`, for pairs of unequal rank:

- the L-polynomial does not change;
- `ε(s, π × σ, ψ^a) = ω_π(a)^(t+1) ω_σ(a)^(r+1) |a|^((r+1)(t+1)(s - 1/2)) ε(s, π × σ, ψ)`
  for `π` on `GL_(r+1)(F)` and `σ` on `GL_(t+1)(F)`, `r ≠ t`, when the
  measure is self-dual for each character.

The source is Cogdell and Piatetski-Shapiro, *Converse theorems for GL_n*,
Publ. Math. IHÉS 79 (1994), 157-214, Lemma 2.1 and its proof. The epsilon
factor of the source is defined with one Haar measure for both characters.
The JPSS relation of the Library uses a measure self-dual for the character.
The exponent of `|a|` therefore differs from the printed one by a computed
term (see Interpretation).

The relations are `IsPadicSymmetricLPolynomial` and
`IsPadicSymmetricEpsilonFactor` (module `PadicPairFactors`). The module
defines three statements. None of them is proved.

## Source

Cogdell and Piatetski-Shapiro 1994 (registered as
`cogdell-piatetski-shapiro-1994-converse`; read from the rendered pages,
0-based PDF index = printed page - 156).

- **§2, printed page 161.** `Π` is a representation of `GL_n(𝔸)` and `τ`
  one of `GL_m(𝔸)`, `1 ≤ m ≤ n - 1`. Each local component is "either
  irreducible or induced of Whittaker type". The local factors
  `L(Π_v × τ_v, s)` and `ε(Π_v × τ_v, s, ψ_v)` are those of the local theory
  [24, 27]: [24] is JPSS 1983 (*Rankin-Selberg convolutions*), [27] the
  Archimedean theory of Jacquet and Shalika.
- **Lemma 2.1 and proof, printed pages 161-162.** To see that the global
  epsilon factor does not depend on `ψ`, the proof computes the change of the
  local factor under `ψ(x) ↦ ψ^λ(x) = ψ(λx)`, `λ ∈ kˣ`. The local epsilon
  factor is defined by the local functional equation
  `Ψ(W, W'; s) / L(Π_v × τ_v, s) · ε(Π_v × τ_v, s, ψ_v) ω_(τ_v)(-1)^(n-1) = Ψ̃(ρ(w_(n,m)) W̃, W̃'; 1 - s) / L(Π̃_v × τ̃_v, 1 - s)`
  with `W ∈ W(Π_v, ψ_v)`, `W' ∈ W(τ_v, ψ_v⁻¹)`, `W̃(g) = W(w_n ᵗg⁻¹)` and
  `W̃'(g) = W'(w_m ᵗg⁻¹)`. Here `w_r` is the longest Weyl element of `GL_r`,
  `w_(n,m) = diag(I_m, w_(n-m))`, and `ρ` is right translation.
- **The integrals, printed page 162.** With `k = n - m - 1`,
  `Ψ(W, W'; s) = ∫_(N_m\GL_m) W(diag(g, I_(n-m))) W'(g) |det g|^(s-(n-m)/2) dg`
  and
  `Ψ̃(W, W'; s) = ∫_(N_m\GL_m) ∫_(M_(k,m)) W([[g, 0, 0], [x, I_k, 0], [0, 0, 1]]) W'(g) |det g|^(s-(n-m)/2) dx dg`.
- **Change of model, printed page 162.** With
  `a_t(λ) = diag(λ^(t-1), λ^(t-2), …, λ, 1) ∈ B_t(k)`, the function
  `g ↦ W(a_n(λ) g)` lies in `W(Π_v, ψ_v^λ)` for `W ∈ W(Π_v, ψ_v)`. "Note that
  the local L-functions are independent of the choice of `ψ_v`." Hence
  `ε(Π_v × τ_v, s, ψ_v^λ)` is defined by the same functional equation for
  `ℓ(a_n(λ)) W` and `ℓ(a_m(λ)) W'`.
- **Computation, printed pages 162-163.**
  `Ψ(ℓ(a_n(λ)) W, ℓ(a_m(λ)) W'; s) = |λ|^(As+B) ω_τ(λ)^(m-n) Ψ(ρ(diag(I_m, a_(n-m)(λ))) W, W'; s)`
  and
  `Ψ̃(ρ(w_(n,m)) (ℓ(a_n(λ)) W)~, (ℓ(a_m(λ)) W')~; 1 - s) = |λ|^(C(1-s)+D) ω_Π(λ)^m ω_τ(λ)^m Ψ̃(ρ(w_(n,m)) (ρ(diag(I_m, a_(n-m)(λ))) W)~, W̃'; 1 - s)`,
  with `A = m(m - n) - m(m-1)/2`, `C = -m² + m(m-1)/2` and explicit `B`, `D`.
- **Result, printed page 163.** "Then using the definition of the
  respective local ε-factors, we find
  `ε(Π_v × τ_v, s, ψ_v^λ) = ω_(Π_v)(λ)^m ω_(τ_v)(λ)^n |λ|_v^(nms-d) ε(Π_v × τ_v, s, ψ_v)`
  with `d = nm - m(m+1)/2`."

## Definitions

Throughout, `F : PadicField p` carries its canonical topological data, `q` is
its residue cardinality, `ψ` is a `UnitaryAdditiveCharacter` of `F`
(continuous and nontrivial), and `ψ.scale a` is the published character
`x ↦ ψ(a x)` (module `HarmonicAnalysis.CharacterTransport`). `ord` is
`F.canonicalTopologicalData.ord`, the normalized valuation, and
`|a| = F.canonicalTopologicalData.normalizedAbs a = q^(-ord a)`. The relation
`IsPadicSymmetricEpsilonFactor F ψ ν π σ e`, `e = (c, m) : ℂˣ × ℤ`, says
`ε(s, π × σ, ψ) = c q^(-ms)` for the pair read with the larger rank first:

- a compatible quotient measure exists;
- the member read first has a nonzero standard Whittaker functional for `ψ`
  and the other one for `ψ⁻¹`;
- for every compatible quotient measure and every pair of nonzero
  functionals, the JPSS functional equation holds with this monomial, for
  every block `j` of the unequal-rank integrals, the integral over the
  rectangular block using the product measure of `ν`.

`IsPadicSymmetricLPolynomial F ψ ν π σ P` says `L(s, π × σ) = 1 / P(q^(-s))`:
a compatible quotient measure exists, and for each of them `P` is the
normalized generator of the integrals of every block.

- `UnequalRankLPolynomialCharacterChangeStatement` quantifies over:
  - every `p`, `F` and all `r`, `t` with `r ≠ t`;
  - representations `π` of `GL_(r+1)(F)` (universe `uV`) and `σ` of
    `GL_(t+1)(F)` (universe `uW`) that are irreducible
    (`Representation.IsIrreducible`) and admissible (`Langlands.IsAdmissible`,
    which includes smoothness);
  - every `ψ`, every additive Haar measure `ν`, every `a : Fˣ` and every
    `P : ℂ[X]`.

  It concludes `IsPadicSymmetricLPolynomial F (ψ.scale a) ν π σ P` from
  `IsPadicSymmetricLPolynomial F ψ ν π σ P`.
- `UnequalRankEpsilonCharacterChangeStatement` quantifies over:
  - every `p`, `F`, all `r ≠ t`, and `π`, `σ` irreducible and admissible as
    above;
  - characters `ωπ ωσ : Fˣ →* ℂˣ` with
    `Classification.HasGLCentralCharacter F (r + 1) π ωπ` and
    `Classification.HasGLCentralCharacter F (t + 1) σ ωσ` (the scalar matrix
    `b · 1` acts by `ωπ(b)`, resp. `ωσ(b)`);
  - every `ψ`, every `ν` in `LocalFactor.PadicAbelian.SelfDualHaar` for `ψ`,
    every `a : Fˣ`, every `ν'` in `SelfDualHaar` for `ψ.scale a`, and every
    `e : ℂˣ × ℤ`.

  From `IsPadicSymmetricEpsilonFactor F ψ ν.val π σ e` it concludes that
  there is `e'` with `IsPadicSymmetricEpsilonFactor F (ψ.scale a) ν'.val π σ e'`,
  `e'.2 = e.2 + (r + 1)(t + 1) · ord a` and
  `e'.1 = e.1 · ωπ(a)^(t+1) · ωσ(a)^(r+1) · |a|^(-(r+1)(t+1)/2)`. The power
  is the complex power of the positive real `|a|`.
- `PairFactorCharacterChangeStatement` is the conjunction of the two
  statements.

## Interpretation

- **Encoding.** With `N = (r + 1)(t + 1)` and `|a| = q^(-ord a)`,
  `ω_π(a)^(t+1) ω_σ(a)^(r+1) |a|^(N(s - 1/2)) · c q^(-ms)` equals
  `c ω_π(a)^(t+1) ω_σ(a)^(r+1) |a|^(-N/2) · q^(-(m + N ord a)s)`. This is
  the conclusion `e' = (c', m + N ord a)`. By uniqueness of epsilon factors
  (`IsPadicSymmetricEpsilonFactor.unique`), `e'` is the epsilon factor of
  the pair for `ψ^a`. The statement also asserts its existence.
- **Ranks and central characters.** In the source `Π` lives on `GL_n` and
  `τ` on `GL_m`, `m < n`, and the factor is `ω_Π(λ)^m ω_τ(λ)^n |λ|^(nm…)`:
  each central character is raised to the rank of the other member. The
  relation `IsPadicSymmetricEpsilonFactor` reads the pair with the larger rank
  first (JPSS (2.12)), and the factor
  `ω_π(a)^(t+1) ω_σ(a)^(r+1) |a|^((r+1)(t+1)(s-1/2))` is symmetric under
  exchanging `(π, r)` with `(σ, t)`. So `r ≠ t` covers both orders. The
  central characters are hypotheses because the computation moves `a_n(λ)`
  past the long Weyl element: `w_n a_n(λ) w_n = λ^(n-1) a_n(λ)⁻¹`, so the
  central character of each member appears.
- **The exponent `d`: measures.** The source's `ε` is defined by one
  functional equation, between the integral `Ψ` (no `x`-integral) and the
  integral `Ψ̃` over `M_(k,m)`, `k = n - m - 1`, with one Haar measure `dx`
  for `ψ` and for `ψ^λ`. The printed `d = nm - m(m+1)/2` is for this
  convention. A check of the printed constants confirms it:
  `-(C + D - B) = nm - m(m+1)/2`. The Library relation is that of JPSS
  Theorem 2.7: one epsilon factor for all blocks `j`, the block integral
  using the product measure of a Haar measure `ν` on `F`. A single factor
  for all blocks depends on the normalization of `ν`, and the relation is
  used with `ν` self-dual for `ψ` (see the Markdown of `GammaFactor` and
  `EpsilonFactor`). The conversion:
  - In the source's equation (the Library's block `j = 0`) only `Ψ̃`
    involves `dx`. Replacing `dx` by `c · dx` multiplies `Ψ̃` by `c^(km)`,
    so it multiplies the source's `ε` by `c^(km)`.
  - The measure self-dual for `ψ^λ` is `|λ|^(1/2)` times the one self-dual
    for `ψ`: the Fourier transform for `ψ^λ` and `c ν` is
    `f̂_λ(y) = c f̂(λy)`, and applying it twice gives `c² |λ|⁻¹ f(-x)`, so
    `c = |λ|^(1/2)`.
  - Taking `dx` self-dual for `ψ`, the factor for `ψ^λ` with its own
    self-dual measure is `|λ|^(km/2)` times the source's factor for `ψ^λ`.
    The exponent of `|λ|` becomes `nms - d + km/2`, and
    `d - km/2 = nm - m(m+1)/2 - m(n-m-1)/2 = nm/2`.

  So with self-dual measures `ε(s, Π × τ, ψ^λ) = ω_Π(λ)^m ω_τ(λ)^n |λ|^(nm(s-1/2)) ε(s, Π × τ, ψ)`.
  For `n = m + 1` (`k = 0`) there is no `x`-integral and both conventions
  give `d = nm/2`. For `GL_3 × GL_1` the author checked both blocks
  `j = 0, 1` by hand (a private check, not in the source). The result agrees with Tate's
  `ε(s, χ, ψ^a) = χ(a) |a|^(s-1/2) ε(s, χ, ψ)` for self-dual measures, and
  with `γ(s, π × σ, ψ) γ(1 - s, π̌ × σ̌, ψ⁻¹) = 1` (the factors for `ψ^a`
  and `(ψ⁻¹)^a` change by inverse amounts). It is also consistent with the
  published `PairEpsilonExponentStatement`: `n(ψ^a) = n(ψ) + ord a`, so the
  exponent `m` grows by `(r+1)(t+1) ord a`.
- **The L-polynomial.** The source states the independence of `ψ` without
  proof. It follows from the change of model `W ↦ W(a_n(λ) ·)` and a change
  of variables in the integrals; the published modules
  `UnequalRankCharacterChange` (`isUnequalRankLPolynomial_characterChange_normalized`)
  prove it block by block, assuming the measure laws
  `HasCharacterChangeMeasureLaw` and `HasCharacterChangeRectangularMeasureLaw`.
  The statement here is unconditional and concerns the p-adic relation.
  The relation does not depend on the scaling of `ν`, so the same `ν` is used
  for both characters.
- **Hypotheses.** The source allows local components that are irreducible or
  induced of Whittaker type. The statements assume irreducible admissible
  representations, a special case. Genericity is not assumed. The epsilon
  relation in the hypothesis already requires nonzero Whittaker functionals.
  In both statements `ℓ ↦ ℓ ∘ π(a_n(λ))` matches the functionals for `ψ`
  with those for `ψ^a` (published
  `characterChangeFunctionalEquiv` and `characterChangeInverseFunctional`,
  module `Whittaker.CharacterChange`, where
  `characterChangeElement a n = diag(a^n, …, a, 1)` is the source's
  `a_(n+1)(a)`).
  For a pair without nonzero functionals no `e` satisfies the hypothesis of
  the epsilon statement, which then holds trivially.
- **Equal rank is not stated.** Lemma 2.1 concerns `m < n`. For `m = n` the
  same formula holds classically, with the Fourier transform of the
  Schwartz-Bruhat function also depending on `ψ`. No original source for it
  was found in the project literature, so it is not stated.
- **Field.** `F` is a p-adic field because the canonical topological data and
  the p-adic relations are published only for `PadicField`. The source works
  at every place of a number field.
- **Not stated.** The global consequence of Lemma 2.1 (independence of the
  global `ε(Π × τ, s)` of `ψ`), and the Archimedean places.

## Universes

All three statements have universe parameters `uF` (the field), `uV` (the
space of `π`) and `uW` (the space of `σ`).

## Lean checks

`lean_check` of the module with declaration
`Langlands.RankinSelberg.PairFactorCharacterChangeStatement`:

- 0 errors and 0 warnings.
- The declaration is a definition returning `Prop`, with universe parameters
  `uF`, `uV`, `uW`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
