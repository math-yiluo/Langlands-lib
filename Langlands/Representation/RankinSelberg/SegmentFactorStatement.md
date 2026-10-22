# L- and gamma factors of pairs of segment representations

Author: Worker 11. This module, in namespace `Langlands.RankinSelberg`, states
the three formulas of Henniart, *Une caractérisation de la correspondance de
Langlands locale pour GL(n)*, Bull. SMF 130 (2002), §2.6, for the factors of
pairs of the essentially square-integrable representations `St_n(ρ)`:

- the L-factor of `St_n(ρ) × St_n'(ρ')`;
- the L-factor of the pair of contragredients;
- the gamma factor of `St_n(ρ) × St_n'(ρ')`.

The module defines one relation with two lemmas, and four statements. None of
the statements is proved.

## Source

Henniart 2002, read from the text layer (printed page = 0-based PDF index +
587).

- **§1.2, printed pages 588-589.** The factors `L(s, π × π')`,
  `ε(s, π × π', ψ)` and
  `γ(s, π × π', ψ) = ε(s, π × π', ψ) L(1 - s, π^∨ × π'^∨) / L(s, π × π')`
  are those of Jacquet, Piatetski-Shapiro and Shalika [6].
- **§2.5, printed pages 594-595.** `i(π_1, …, π_r)` is normalized parabolic
  induction from the upper block-triangular parabolic subgroup with diagonal
  blocks of sizes `n_1, …, n_r`. `ν` is the quasi-character of `F^×` given by
  the normalized absolute value, and `χπ` is the class of
  `g ↦ χ(det g) π(g)`.
- **§2.6, printed page 595.** For `ρ ∈ A_0` (irreducible supercuspidal) and
  `n ≥ 1`, the representation `i(ρ, νρ, …, ν^(n-1) ρ)` has a unique
  irreducible quotient, essentially square-integrable, whose class is
  `St_n(ρ)` ([11, 9.3], Zelevinsky). The computations of [6] (mainly its
  introduction) give, for `(ρ, n), (ρ', n')`:
  - `L(s, St_n(ρ) × St_n'(ρ')) = ∏_j L(s, ν^(n+n'-1-j) ρ × ρ')`, with `j`
    from `1` to `min(n, n')`;
  - `L(s, St_n(ρ)^∨ × St_n'(ρ')^∨) = ∏_j L(s, ν^(1-j) ρ^∨ × ρ'^∨)`, same
    range of `j`;
  - since gamma factors are multiplicative for normalized induction,
    `γ(s, St_n(ρ) × St_n'(ρ'), ψ) = ∏_(i=1)^n ∏_(j=1)^(n') γ(s, ν^(i+j-2) ρ × ρ', ψ)`.

  Henniart adds that this also controls the epsilon factors but does not give
  their expression (§2.4: "nous n'en avons pas besoin").

## Definitions

- `IsPadicRankGammaFactor F ψ ν π σ G` is `γ(s, π × σ, ψ) = G(q^(-s))` for
  representations `π` of `GL_n(F)` and `σ` of `GL_t(F)` of arbitrary ranks.
  It is the published `IsPadicSymmetricGammaFactor` when both ranks are
  successors and `False` when one rank is `0`. It is the gamma analogue of the
  published `IsPadicRankLPolynomial` (module
  `LanglandsQuotientLFactorStatement`); both are needed because
  `Δ.degree = Δ.length * Δ.rank` is not syntactically a successor.
  - `isPadicRankGammaFactor_succ`: for successor ranks the relation is
    `IsPadicSymmetricGammaFactor` (by definition).
  - `IsPadicRankGammaFactor.unique`: the factor is unique, from
    `IsPadicSymmetricGammaFactor.unique`.

## Statements

All three statements quantify over:

- every prime `p` and every `F : PadicField p` with its canonical topological
  data;
- every `UnitaryAdditiveCharacter` `ψ` and every `ν` in the published
  `LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`;
- every pair of segments `Δ` (carriers in `uV`) and `Δ'` (carriers in `uW`)
  of the published `Segment` (module `Classification/Segments`). `Δ.base` is
  the class of `ρ`, `Δ.length` is `n` and `Δ.rank` is the rank of `ρ`;
- every smooth `π` of `GL_(Δ.degree)(F)` and `σ` of `GL_(Δ'.degree)(F)` with
  `IsSegmentHead Δ π` and `IsSegmentHead Δ' σ`. This published relation says
  that `π` is an irreducible quotient of `i(A, νA, …, ν^(n-1) A)` for a
  supercuspidal representative `A` of `ρ`, and that all irreducible quotient
  maps have the same kernel. So `π` is a representative of `St_n(ρ)`;
- every supercuspidal representative `A` of `Δ.base` and `A'` of `Δ'.base`
  (`CuspidalDatum.IsRepresentedBy`). The twist `ν^x A` is
  `realPowerTwist (determinantNorm Δ.rank) x A`, the same twist
  `g ↦ |det g|^x A(g)` as the published `segmentFactor` used to build the
  induced representation.

The index ranges are shifted by one: Lean's `j : Fin (min n n')` is
Henniart's `j - 1`, and Lean's `i : Fin n`, `j : Fin n'` are his `i - 1`,
`j - 1`.

- `SegmentHeadLFactorStatement` (first display): there are polynomials `P`
  and `Q j` with
  - `IsPadicRankLPolynomial F ψ ν π σ P`;
  - for each `j : Fin (min n n')`,
    `IsPadicRankLPolynomial F ψ ν (ν^(n+n'-2-j) A) A' (Q j)`, where the
    exponent is computed in `ℝ`;
  - `P = ∏ j, Q j`.
- `SegmentHeadContragredientLFactorStatement` (second display): the same
  with `smoothContragredient` of `π`, `σ`, `A`, `A'`, and with
  `ν^(-j) A^∨` in place of `ν^(n+n'-2-j) A`.
- `SegmentHeadGammaFactorStatement` (third display): there are rational
  functions `G` and `H i j` with
  - `IsPadicRankGammaFactor F ψ ν π σ G`;
  - for each `i : Fin n` and `j : Fin n'`,
    `IsPadicRankGammaFactor F ψ ν (ν^(i+j) A) A' (H i j)`;
  - `G = ∏ i, ∏ j, H i j`.
- `SegmentHeadFactorStatement` is the conjunction of the three.

Since the relations are unique (`IsPadicRankLPolynomial.unique`,
`IsPadicRankGammaFactor.unique`), each statement says that the factors exist
and that the factor of the segment pair equals the product.

## Interpretation

- **Existence is part of the conclusion.** The relations of `PadicPairFactors`
  require Whittaker functionals, so the statements include that the factors of
  `St_n(ρ) × St_n'(ρ')` exist. This holds because `St_n(ρ)` is generic
  (Zelevinsky, Theorem 9.7(a), stated in the Library's
  `SegmentGenericStatement` module); the factors of the supercuspidal pairs
  exist for the same reason. Henniart takes
  this for granted, as JPSS define the factors for all generic pairs.
- **Classes and representatives.** Henniart works with classes; here `π`,
  `σ`, `A`, `A'` are arbitrary representatives. The relations are invariant
  under equivalence (`congr_equiv` lemmas of `PadicPairFactors`), and so is
  twisting, so this is the class statement.
- **Consistency with JPSS.** The first display agrees with JPSS (8.2), where
  `St_m(ρ)` is the quotient attached to the segment with exponents
  `ν^0, …, ν^(m-1)`. When the ranks of `ρ` and `ρ'` differ, all the
  L-factors involved are `1` (JPSS (8.1)(i)), and the two L formulas hold
  trivially; the gamma formula is still a nontrivial product of monomials.
- **The contragredient formula** follows from the first display and
  `St_n(ρ)^∨ ≃ St_n(ν^(1-n) ρ^∨)`, because
  `(n + n' - 1 - j) + (1 - n) + (1 - n') = 1 - j`. The text layer of
  page 595 prints the identity as `St_n(ρ)^∨ ≃ ν^(1-n) St_n(ρ)`, without the
  `∨` on `ρ`; Galois-side §2.3 has the matching identity `St_n^∨ ≃ ν^(1-n) ⊗ St_n`.
  The contragredient identity is not restated here; it is part of the
  Library's `SegmentConstituentContragredientCompatibility` (Ze80
  Propositions 3.3 and 9.4: the contragredient of the head for `Δ` is the
  head for `Δ^∨ = [(ν^(n-1) ρ)^∨, ρ^∨]`).
- **Not stated.** No epsilon formula, since Henniart gives none. The bijection
  `A_0 × ℕ^* → A_2`, the uniqueness of the quotient and the
  square-integrability of `St_n(ρ)` are Zelevinsky's theorems. The relation
  `IsSegmentHead` takes the uniqueness of the quotient as a hypothesis.
- **Measures and field.** As in the other units, `ν` is self-dual for `ψ`.
  `F` is a p-adic field (`PadicField`) because the canonical topological data
  and segments are published only for p-adic fields; Henniart's `F` is any
  nonarchimedean local field.

## Lean checks

`lean_check` of the module with declaration
`Langlands.RankinSelberg.SegmentHeadFactorStatement`:

- 0 errors and 0 warnings.
- The declaration is a definition returning `Prop`, with universe parameters
  `uF`, `uV`, `uW`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
