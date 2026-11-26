# Regular-patch Eisenstein comparison for finite families of inducing data

Module `Langlands.Global.AdelicEisensteinStandardFamilyComparisonStatement` states
`Langlands.Global.StandardEisensteinFamilyComparisonStatement` as a proposition. It supplies no
proof.

## Statement

The setting consists of:

- a number field `F`, an affine group `G` of finite type over `F`, and a compatible family
  `fam` of standard parabolics for one maximal split torus, one generic cocharacter and one
  choice of coroots (`StandardParabolicFamily`, which includes connected reductivity);
- standard indices `I` and `Q`, with parabolics `P_I = M_I U_I` and `P_Q = M_Q U_Q`;
- a rational point `n` of the normalizer of the maximal split torus, `c : M_Q → M_I` and
  `proj : P_Q → M_Q` with `l_Q ≫ proj = 𝟙`, such that `IsWeylConjugation` holds for
  `(P_I, P_Q, n, c)`. The class `w` of `n` in the relative Weyl group sends every simple root
  in `I` into `Q`, and `w⁻¹` sends every simple root in `Q` into `I`;
- a maximal compact subgroup `K` of `G(𝔸)` with `P_I(𝔸)K = P_Q(𝔸)K = P_∅(𝔸)K = G(𝔸)` and
  `K ∩ M_J(𝔸)` maximal compact in every standard Levi `M_J(𝔸)`. This is the good position of
  Bernstein–Lapid §2.1;
- a closed matrix embedding `rho` of any size, with smooth-structure data `hsmooth` and
  `hcalc`. The archimedean part of `K` is `K_∞ = K.comap (ofInfinite F G)`.

The new data are a finite family of inducing forms with coefficients:

- `φ : Fin p → (G(𝔸) → ℂ)`, each `φ v` automorphic on `U_I(𝔸) M_I(F) \ G(𝔸)` for `K_∞` and
  `rho`;
- `b : Fin p → (X^*(P_I) ⊗ ℂ → ℂ)`, each `b v` meromorphic with domain of holomorphy `Db`
  (`IsMeromorphicInCoordinatesOn`).

The hypotheses are:

- every scalar function `λ ↦ EP λ g` is meromorphic with domain of holomorphy `DP`, and for some
  `R`, at every `λ` that is `R`-regular for the standard presentation of `P_I` and every `g`,
  `EP λ g = ∑ v, b v λ * hKI.eisensteinSeries (φ v) λ g`;
- `ψ : Fin k → (G(𝔸) → ℂ)` are automorphic on `U_Q(𝔸) M_Q(F) \ G(𝔸)`, the coefficients
  `coeff i` are meromorphic with domain `D`, and for some `R`, at every `R`-regular `λ` and every
  `g`,
  `∑ v, b v λ * hKI.intertwiningOperator hKQ (iU I) (l I) (iU Q) c proj n (φ v) λ g
    = ∑ i, coeff i λ * ψ i g`.

The conclusion holds for every real `R`. There are a linear coordinate system
`e : ℂᵐ ≃ X^*(P_I) ⊗ ℂ` and a nonempty open set `O ⊆ ℂᵐ` with two properties at every
`x ∈ O`:

1. `wλ = weylParameter (l I) c proj (e x)` is `R`-regular for the standard presentation of
   `P_Q`;
2. at every `g ∈ G(𝔸)`,
   `EP (e x) g = ∑ i, coeff i (e x) * hKQ.eisensteinSeries (ψ i) (wλ) g`.

The regularity predicates are those of `ParabolicRootPresentation.IsRegularParameter` for the
presentations `⟨⟨T, i, ν, I, f I⟩, isCompatible I⟩` and `⟨⟨T, i, ν, Q, f Q⟩, isCompatible Q⟩` of
the family, with the split-torus witnesses of the family.

For `p = 1`, `b 0 = 1` and `Db` the whole space, this is the comparison for a single inducing
form `φ 0`.

## Source and provenance

Provenance: derived. J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`:

- §2.1, pp. 189–190: the standard parabolics of a fixed minimal parabolic, the compact `K` in
  good position, and `W(P, Q)`;
- §8.6, p. 225 (TeX `1911.02342.tex`, lines 3495–3512): for `w' ∈ W(P, P')` and
  `⟨w' Re λ, α^∨⟩ ≫ 0` for all simple roots `α` of `P'`, the leading cuspidal components of
  `E(M(w', λ)φ, w'λ)` and of `E(φ, λ)` agree, and Theorem 6.3 gives
  `E(M(w', λ)φ, w'λ) = E(φ, λ)`.

The statement applies this identity to the inducing datum `∑ v, b v λ · φ v`, whose
coefficients depend on `λ`. In the region of absolute convergence the Eisenstein series and the
intertwining operator are linear in the inducing function, so the left side of the identity is
`∑ v, b v λ · E(φ v, λ)` and the right side is the series of `∑ v, b v λ · M(w, λ)(φ v)`. The
hypotheses give a meromorphic continuation `EP` of the first expression and write the second
inducing datum as the finite meromorphic combination `∑ i, coeff i λ · ψ i`.

Such families arise when the Iwasawa compact is changed. If two maximal compacts `K` and `K'`
with `P(𝔸)K = P(𝔸)K' = G(𝔸)` have the same archimedean part, the twist `φ_λ` for `K` is a finite
sum `∑ v, exp⟨λ, v⟩ · (φ_v)_λ` of twists for `K'` of fixed automorphic forms `φ_v`
(`EisensteinFiniteCompactChangeStatement`, module
`Langlands.Global.AdelicEisensteinFiniteCompactChangeStatement`). The same coefficients then
relate the Eisenstein series and the intertwining operators
(`EisensteinFiniteCompactOperatorComparisonStatement`, module
`Langlands.Global.AdelicEisensteinFiniteCompactOperatorComparison`). The coefficients
`exp⟨λ, v⟩` are entire in `λ`. The present statement allows any meromorphic coefficients.

The statement holds for arbitrary continuations. Any `EP` of the hypotheses agrees with
`∑ v, b v λ · E'_v(λ)`, where `E'_v` is the continuation of `E(φ v, λ)` given by Theorem 2.3 (1),
on the intersection of their domains, by uniqueness of scalar meromorphic continuation from the
regular region. The open patch can therefore be chosen inside the common domains, where the
cited identity applies.
