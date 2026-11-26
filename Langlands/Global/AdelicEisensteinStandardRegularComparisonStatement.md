# Regular-patch Eisenstein comparison for one standard family

Module `Langlands.Global.AdelicEisensteinStandardRegularComparisonStatement` states
`Langlands.Global.StandardEisensteinRegularComparisonStatement` as a proposition. It
supplies no proof.

## Statement

The data are a number field `F`, an affine group `G` of finite type over `F`, and a
compatible family `fam` of standard parabolics for one maximal split torus, one generic
cocharacter and one choice of coroots (`StandardParabolicFamily`, which includes
connected reductivity). Two standard indices `I` and `Q` give the parabolics
`P_I = M_I U_I` and `P_Q = M_Q U_Q`.

- `n` is a rational point of the normalizer of the maximal split torus, `c : M_Q → M_I` and
  `proj : P_Q → M_Q` with `l_Q ≫ proj = 𝟙`, such that `IsWeylConjugation` holds for
  `(P_I, P_Q, n, c)`. Thus `n M_I n⁻¹ = M_Q`, and `c` is conjugation by `n⁻¹`.
- With `w` the class of `n` in the relative Weyl group, `w` sends every simple root in `I`
  into `Q` and `w⁻¹` sends every simple root in `Q` into `I`. So `w` is a bijection from the
  simple roots of `M_I` onto those of `M_Q`.
- `K` is a maximal compact subgroup of `G(𝔸)` with `P_I(𝔸)K = P_Q(𝔸)K = G(𝔸)`,
  `P_∅(𝔸)K = G(𝔸)` for the minimal standard parabolic, and `K ∩ M_J(𝔸)` maximal compact in
  every standard Levi `M_J(𝔸)`. This is the good position of Bernstein–Lapid §2.1.
- `rho` is a closed matrix embedding of any size, with smooth-structure data `hsmooth` and
  `hcalc`. The archimedean part of `K` is `K_∞ = K.comap (ofInfinite F G)`.
- `φ` is automorphic on `U_I(𝔸) M_I(F) \ G(𝔸)` for `K_∞` and `rho`.
- `EP : X^*(P_I) ⊗ ℂ → (G(𝔸) → ℂ)` and `DP` are such that every scalar function
  `λ ↦ EP λ g` is meromorphic with domain of holomorphy `DP`
  (`IsMeromorphicInCoordinatesOn`). For some `R`, `EP λ = hKI.eisensteinSeries φ λ` whenever
  `λ` is `R`-regular for the standard presentation of `P_I`.
- `ψ : Fin k → (G(𝔸) → ℂ)` are automorphic on `U_Q(𝔸) M_Q(F) \ G(𝔸)`. The coefficients
  `coeff i` are meromorphic with domain `D`, and for some `R`, at every `R`-regular `λ` and
  every `g`,
  `hKI.intertwiningOperator hKQ (iU I) (l I) (iU Q) c proj n φ λ g = ∑ i, coeff i λ * ψ i g`.

The conclusion holds for every real `R`. There are a linear coordinate system
`e : ℂᵐ ≃ X^*(P_I) ⊗ ℂ` and a nonempty open set `O ⊆ ℂᵐ` with two properties at every
`x ∈ O`:

1. `wλ = weylParameter (l I) c proj (e x)` is `R`-regular for the standard presentation of
   `P_Q`;
2. at every `g ∈ G(𝔸)`,
   `EP (e x) g = ∑ i, coeff i (e x) * hKQ.eisensteinSeries (ψ i) (wλ) g`.

The regularity predicates are those of `ParabolicRootPresentation.IsRegularParameter` for
the presentations `⟨⟨T, i, ν, I, f I⟩, isCompatible I⟩` and `⟨⟨T, i, ν, Q, f Q⟩, isCompatible Q⟩`
of the family, with the split-torus witnesses of the family.

## Source and relation to the general statement

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024):

- §2.1, pp. 189–190: the standard parabolics of a fixed minimal parabolic, the compact `K`
  in good position, and `W(P, Q)`.
- §8.6, p. 225 (TeX `1911.02342.tex`, lines 3495–3512): for `w' ∈ W(P, P')` and
  `⟨w' Re λ, α^∨⟩ ≫ 0` for all simple roots `α` of `P'`, the leading cuspidal components of
  `E(M(w', λ)φ, w'λ)` and of `E(φ, λ)` agree, and Theorem 6.3 gives
  `E(M(w', λ)φ, w'λ) = E(φ, λ)`.

The statement is this identity in BL's setting, written for arbitrary continuation data, as
in `EisensteinFunctionalEquationRegularComparisonStatement`
(`Langlands/Global/AdelicEisensteinFunctionalEquationRegularComparisonStatement.lean`). The
sum `∑ i, coeff i λ · ψ i` is the continued intertwining datum. Its convergent `P_Q`-series
at `wλ` is `∑ i, coeff i λ · E(ψ i, wλ)`, and `EP` is the continuation of `E(φ, λ)`. The
general statement allows parabolics with arbitrary root presentations, an arbitrary Weyl
point and a compact `K` that only covers `P` and `Q`. Here instead the parabolics are standard
for one family, the Weyl element is a normalizer point matching the simple roots, and `K` is
in good position, which is the setting of the cited source. The bound `R` can be fixed in
advance because the comparison holds on a region where `wλ` is arbitrarily regular.

The statement holds for arbitrary continuations. Any `EP` of the hypotheses agrees with the
continuation of Theorem 2.3 (1) on the intersection of their domains, by uniqueness of
scalar meromorphic continuation from the regular region. The open patch can therefore be
chosen inside the common domains, where the cited identity applies.
