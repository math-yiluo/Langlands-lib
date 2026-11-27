# Subunitary exponents of constant terms of Eisenstein series at unitary parameters

Module `Langlands.Global.AdelicEisensteinUnitaryExponentStatement`, namespace
`Langlands.Global`. It defines two predicates on a `StandardParabolicFamily`,
`IsDominantSplitPoint` and `HasSubunitaryShiftEquations`, states one proposition,
`EisensteinUnitaryExponentStatement`, and proves nothing.

## Sources

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*,
  Clay Math. Proc. 13 (2011), 309–331, registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (printed page `n` is PDF page
  `n + 9`): Proposition 4, printed p.321 (the constant term of `E_P(·, φ, λ)` along `Q` is
  `∑_{w ∈ _QΩ_P} E^Q_{Q_w}(·, M(w, λ) φ_{P_w}, wλ)`), the decomposition (12) and the inclusion
  of exponents (13), printed p.322, valid by analytic continuation wherever the series and the
  relevant intertwining operators are regular; Lemma 6, printed p.322 (for `φ ∈ A^2_P` and
  `μ ∈ E_{P_w}(φ)`, `Re⟨wμ, ϖ^∨⟩ ≤ 0` for every `ϖ ∈ Δ̂_{Q_w}`, by Mœglin–Waldspurger I.4.11);
  Proposition 6, printed pp.329–330 (holomorphy of `E(φ, λ)` on `i𝔞_P^*` for `φ ∈ A^2_P`).
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), 187–234, registered as
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`: Theorem 2.3, p.191 (meromorphic
  continuation of `λ ↦ E(φ, λ)` with values in the functions of uniform moderate growth), and
  the Corollary at the end of §8.6, p.226 (the continuation locally in the Fréchet spaces of
  §7.1, pp.210–211).
- P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered
  as `delorme-2023-spectral-theorem-langlands` (published PDF numbering): §2, p.6 (the closed
  chamber `𝔞_P^+` and the definition of subunitary `ν ∈ 𝔞_{P,ℂ}^*`, `Re ν(X) ≤ 0` for
  `X ∈ 𝔞_P^+`, with the equivalent test (2.1) on `𝔞_0^+`); §3.1, p.10 (the normalized exponent
  expansion (3.2)); §4.1, pp.16–17 (the constant-term formula (4.2), the weak constant term
  (4.3) at unitary `λ`, and (4.4): for `λ ∈ i𝔞_P^*` the remaining part `E_P(·, φ, λ)^-_Q` is an
  exponential polynomial along `𝔞_Q` with exponents in a set built from `E^-_Q(λ)` by
  repetitions whose multiplicities depend only on those of the exponents of `φ`).
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`: I.3.1–I.3.2, pp.40–42 (the
  exponent decomposition of an automorphic form on `U(𝔸)M(F) \ G(𝔸)` and the generalized
  translation action), I.4.11, pp.74–75 (the cuspidal exponents of square-integrable forms),
  and Lemma I.4.1, p.49 (named in "Use").

Provenance: derived. The statement collects the cited facts for `λ` in a compact subset of
`i𝔞_P^*` and expresses "the exponents of the constant term are subunitary, with at most `m`
of them counted with multiplicity" by the difference equations these exponents impose along the
dominant points of the positive split component.

## Definitions

Let `𝓕` be a `StandardParabolicFamily F G`, `J` a standard index, `P_J = M_J U_J` the standard
parabolic with split component `A_J → M_J`, and `𝔄_J = 𝓕.positiveSplitComponent J`, the image
in `P_J(𝔸)` of the positive real points `A_J(𝔸)^+ = PositiveRealTorus.intrinsicSubgroup F
(𝓕.A J)`.

### `IsDominantSplitPoint J s`

For `s ∈ A_J(𝔸)^+`: every simple root `α ∉ J` satisfies `|α(s)| ≥ 1`, where `α(s)` is the value
of the restriction `𝓕.f J ≫ α` of `α` along `A_J → T` and `|·|` is the idele norm
(`PositiveRealTorus.normCharacter`). In terms of `H_J : 𝔄_J → 𝔞_J`, this is `H_J(s) ∈ 𝔞_J^+`,
the closed positive chamber of `𝔞_J`.

### `HasSubunitaryShiftEquations J m φ`

For every dominant `s ∈ A_J(𝔸)^+`, with image `a ∈ 𝔄_J` (`PositiveRealTorus.positivePointMap`),
there are `w_0, …, w_{m-1} ∈ ℂ` with

- `|w_k| ≤ |a^{ρ_J}| = δ_{P_J}(a)^{1/2}` (`𝓕.halfModulus J a`);
- `IsTranslationPolynomialSolution a' (∏_k (X - w_k)) φ`, where `a'` is the image of `a` in
  `G(𝔸)`: `∑_k c_k φ(a'^k g) = 0` for every `g`, with `∏_k (X - w_k) = ∑_k c_k X^k`.

*Relation to exponents.* Suppose `φ = ∑_{μ ∈ s} φ_μ` where each `φ_μ` has normalized exponent
`μ ∈ 𝔞_{J,ℂ}^*` along `𝔄_J` with polynomial part of degree at most `d_μ`
(`HasExponent`, `HasPolynomialOrbit`), every `μ` is subunitary (`Re μ ≤ 0` on `𝔞_J^+`, Delorme's
definition), and `∑_μ (d_μ + 1) ≤ m`. For `a ∈ 𝔄_J`, the Library's
`HasExponent.exists_isTranslationPolynomialSolution_pow` and
`isTranslationPolynomialSolution_sum_prod` give the equation with roots `a^{μ + ρ_J}`, each
repeated `d_μ + 1` times (pad with roots `0` up to `m`). For dominant `a`,
`|a^{μ + ρ_J}| = e^{Re μ(H_J(a))} |a^{ρ_J}| ≤ |a^{ρ_J}|`. Hence `φ` satisfies
`HasSubunitaryShiftEquations J m φ`. The predicate only records these equations; it does not
assert an exponent decomposition.

## The statement

The data and hypotheses are those of `EisensteinUniformTemperednessStatement`: `φ ∈ A^2_P`
and a continuation `(E, D)` of `E(φ, λ)` with `D ⊇ i𝔞_P^*`. For real linear coordinates
`e : ℝⁿ ≃ X^*(P) ⊗ ℝ` and compact `C ⊆ ℝⁿ` the conclusion is: there is `m : ℕ` such that for
every standard parabolic family `𝓕` of `G`, every standard index `J` and every `x ∈ C`,

`𝓕.HasSubunitaryShiftEquations J m (𝓕.constantTerm J (E (imaginaryParameter F P (e x))))`.

## Why it is true

The following outline explains the statement; it is not proved here. Write `Q = P_J`, and
`E(λ)` for `E_P(·, φ, λ)`.

1. *Families.* Two standard parabolic families are conjugate under `G(F)`, since minimal
   parabolic subgroups and their maximal split tori are. If `γ ∈ G(F)` conjugates `𝓕` to `𝓕'`,
   left `G(F)`-invariance of `E(λ)` shows that the constant term along `γ P_J γ⁻¹` is
   `g ↦ E(λ)_{P_J}(γ⁻¹ g)`, and the shift by `γ a γ⁻¹` corresponds to the shift by `a`. So the
   equations carry over with the same roots and the same half modulus, and one `m` serves all
   families. Fix `𝓕` from now on.
2. *Standard position.* Choose `γ ∈ G(F)` with `P' = γ P γ⁻¹` standard in `𝓕`, and transport
   `K`, `φ` and `λ` by conjugation, as in "Non-standard parabolics" in
   `AdelicWavePacketCompletenessReduction.md`. The transported series satisfies
   `E'(λ')(γ g γ⁻¹) = E(λ)(g)`, and by left `G(F)`-invariance `E(λ)(g) = E'(λ')(g γ⁻¹)`. Right
   translation commutes with constant terms and with the left shifts, so it suffices to treat
   `E'`. Next compare `K' = γ K γ⁻¹` with a maximal compact subgroup `K₀` in good position, as
   in the item "The compact subgroup" of `AdelicEisensteinConvergenceStatement.md`: the series
   for `K'` is a finite sum `∑_j exp⟨λ, c_j⟩ E^{K₀}(φ_j, λ)(· n)` with coefficients entire in
   `λ`, where each `φ_j` is `φ'(· n⁻¹)` times the indicator of a left `P'(𝔸_f)`-invariant open
   and closed set. Such indicators factor out of constant terms along parabolics contained in
   `P'`, so the exponents of the constant terms of every `φ_j`, with their polynomial degrees,
   are among those of `φ'`. Every summand therefore has constant terms whose exponents lie in
   the same finite list with the same degree bounds described below, and so has the sum. The
   order bound does not depend on the number of summands.
3. *Regular parameters.* For `Re λ` sufficiently regular, Lapid's Proposition 4 (Mœglin–
   Waldspurger II.1.7 without cuspidality) writes `E(λ)_Q` as a sum over `w ∈ _QΩ_P` of Levi
   Eisenstein series `E^Q_{Q_w}(·, M(w, λ) φ_{P_w}, wλ)`. In (12) this is split into the
   leading sum `M_Q` over `w ∈ Ω(P; Q)` and the remainder `E_Q`.
   - *Leading sum.* For `w ∈ Ω(P; Q)`, `w M_P w⁻¹ ⊆ M_Q`, so `P_w = P` and
     `A_Q ⊆ w A_P w⁻¹`. The split component `A_Q` is central in `M_Q`, and `a ∈ 𝔄_Q` acts on
     the summand by the character `a ↦ a^{wλ + ρ_Q}`, with normalized parameter `(wλ)|_{𝔞_Q}`.
     Each leading summand contributes one factor `X − a^{wλ + ρ_Q}`.
   - *Remainder.* By (13) with `R = Q`, the exponents of `E_Q` are contained in
     `⋃_{w ∈ _QΩ_P \ Ω(P; Q)} [w(E_{P_w}(φ) + λ)]_Q`. The polynomial degrees are bounded,
     independently of `λ`, in terms of the multiplicities of the exponents of the finitely many
     constant terms `φ_{P_w}`; Delorme's (4.4) records this for the corresponding remainder at
     unitary `λ`. An exponent `ν` with polynomial part of degree `d` contributes the factor
     `X − a^{ν + ρ_Q}` repeated `d + 1` times.

   The product of all these factors annihilates `E(λ)_Q` under left translation by `a` (the
   Library's `HasExponent.exists_isTranslationPolynomialSolution_pow` and
   `isTranslationPolynomialSolution_sum_prod`). Its degree is bounded by a number `m` that
   depends only on `_QΩ_P` and on the exponents of the constant terms of `φ`, and it is padded
   with roots `0` up to `m`. Coinciding roots cause no difficulty.
4. *Imaginary parameters.* Bernstein–Lapid (Theorem 2.3 and the Corollary at the end of §8.6,
   p.226) continue `λ ↦ E(φ, λ)` meromorphically, locally in `λ`, into Fréchet spaces of
   smooth functions of uniform moderate growth at a fixed level, and Lapid's Proposition 6 gives
   holomorphy of the continuation at the points of `i𝔞_P^*`. The constant term at a point is the
   integral of a continuous function over the compact quotient `U_Q(F) \ U_Q(𝔸)`, a continuous
   linear functional on such a space. Hence `λ ↦ E(λ)_Q(a^k g)` is meromorphic on the whole
   parameter space and holomorphic near `i𝔞_P^*`. The supplied `E` agrees with this
   continuation near `i𝔞_P^*`: for each `g` both are meromorphic, both equal the Eisenstein
   series on the regular region, and meromorphic continuation from a nonempty open set is
   unique. The roots `a^{ν + ρ_Q}` above are entire in `λ`, so the coefficients `c_k(λ)` of the
   product are entire, and
   `λ ↦ ∑_k c_k(λ) E(λ)_Q(a^k g)` is meromorphic, holomorphic near `i𝔞_P^*` and zero on the
   regular region. It therefore vanishes at every point of `i𝔞_P^*`.
5. *Subunitarity.* For `λ ∈ i𝔞_P^*` the leading roots satisfy `|a^{wλ + ρ_Q}| = a^{ρ_Q}`. For
   the remainder, `Re[w(μ + λ)]_Q = [w Re μ]_Q`. Lapid's Lemma 6 gives `Re⟨wμ, ϖ^∨⟩ ≤ 0` for
   `ϖ ∈ Δ̂_{Q_w}`, which contains `Δ̂_Q`, and `wμ` vanishes on `𝔞_G`; so `Re[wμ]_Q ≤ 0` on
   `𝔞_Q^+`, that is, the exponent is subunitary in Delorme's sense (§2, p.6). For dominant
   `a`, `|a^{ν + ρ_Q}| = e^{Re ν(H_Q(a))} a^{ρ_Q} ≤ a^{ρ_Q} = δ_Q(a)^{1/2}`.

## Use

In the proof of Delorme 2023, Proposition 4.1, Mœglin–Waldspurger's Lemma I.4.1 (p.49) is
applied uniformly to the Eisenstein series at the parameters of a compact subset of
`i𝔞_P^*`. That lemma bounds an automorphic form on a Siegel set by a sum, over the standard
parabolics `P'`, of the weights `m_{P_0}(g)^{Re π + ρ_{P'}}` times powers of the logarithm, with
`π` running through the cuspidal data of the constant term along `P'`. Delorme's uniform
application needs two inputs: the family is bounded in a space of functions of given moderate
growth, and its constant terms have uniformly controlled cuspidal data ("whose constant terms
uniformly satisfy the assumption of that lemma"). This statement
supplies the second input in the form of difference equations: along the dominant points of
every `𝔄_J` the exponents are subunitary and their number, counted with multiplicity, is
bounded.

## Scope

The statement asserts no constant-term formula, no exponent decomposition and no bound on the
functions. For `J` the index of `G` itself the condition concerns the central exponents of
`E(λ)` along the split centre. Nothing is proved here.
