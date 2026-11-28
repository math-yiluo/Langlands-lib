# Exponent labels of constant terms of Eisenstein series at regular parameters

Module `Langlands.Global.AdelicEisensteinConstantTermExponentLabelsStatement`, namespace
`Langlands.Global`. It states one proposition, `EisensteinConstantTermExponentLabelsStatement`,
and proves nothing. It imports `Langlands.Global.AdelicEisensteinUnitaryExponentStatement` for
the predicate `StandardParabolicFamily.IsDominantSplitPoint` and
`Langlands.Global.AdelicExponentPolynomials` for `StandardParabolicFamily.HasPolynomialOrbit`.

## Sources

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*,
  Clay Math. Proc. 13 (2011), 309–331, registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (printed page `n` is PDF page
  `n + 9`):
  - Proposition 4, printed p.321: for `φ ∈ A_P` and `Re λ` sufficiently regular in the positive
    Weyl chamber, the constant term of `E_P(·, φ, λ)` along `Q` is
    `∑_{w ∈ _QΩ_P} E^Q_{Q_w}(·, M(w, λ) φ_{P_w}, wλ)`;
  - (12) and (13), printed p.322: the splitting of this sum into the part `M_Q` over
    `w ∈ Ω(P; Q)` (those `w` with `w M_P w⁻¹ ⊆ M_Q`) and the remainder `E_Q`, and the inclusion
    of the exponents of the remainder in `⋃_{w ∈ _QΩ_P \ Ω(P; Q)} [w(E_{P_w}(φ) + λ)]_Q`;
  - Lemma 6, printed p.322: for `φ ∈ A^2_P`, `w ∈ _QΩ_P`, `μ ∈ E_{P_w}(φ)` and
    `ϖ ∈ Δ̂_{Q_w}`, `Re⟨wμ, ϖ^∨⟩ ≤ 0` (via Mœglin–Waldspurger I.4.11).
- P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered
  as `delorme-2023-spectral-theorem-langlands` (published PDF numbering):
  - §2, p.6: the closed chamber `𝔞_P^+ = {X ∈ 𝔞_P : α(X) ≥ 0, α ∈ Δ_P}` and the definition of
    subunitary `ν ∈ 𝔞_{P,ℂ}^*`: `Re ν(X) ≤ 0` for every `X ∈ 𝔞_P^+`;
  - §4.1, pp.16–17: the constant-term formula (4.2), the statement that the exponents of
    `E_P(·, φ, λ)_Q` are given by Lapid's (13) and are subunitary for unitary `λ` by Lapid's
    Lemma 6, and (4.4): the remainder is an exponential polynomial along `𝔞_Q` whose exponents
    lie in a set built from `E^-_Q(λ) = ⋃_s {s(E_{P_s}(φ) + λ)|_{𝔞_Q}}` by repetitions with
    multiplicities depending only on those of the exponents of `φ`.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`: II.1.7 (the constant term
  of cuspidal Eisenstein series, which Lapid's Proposition 4 generalizes) and I.4.11 (the
  cuspidal exponents of square-integrable forms).

Provenance: derived. The statement collects, for `λ` in a region where the Eisenstein series
converges, the cited description of the constant terms: a finite sum of polynomial-exponential
terms along `𝔄_Q` whose exponents are affine functions of `λ`, with the counts and degrees of
(4.4), together with Lapid's Lemma 6 and the unitarity of the leading exponents, read off at the
unitary parameters. The sources state these facts for one fixed standard parabolic `P` and a
compact subgroup in good position; the statement asks for them for every standard parabolic
family, as explained under "Correspondence with the sources".

## The statement

The data and hypotheses are those of `EisensteinUnitaryExponentStatement` up to the hypothesis
`IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l φ`, that is `φ ∈ A^2_P`:
a number field `F`, a connected reductive `G`, a parabolic `p : P → G` with geometric unipotent
radical `iU`, a rational Levi `l : M → P`, a root presentation `r` of a split component
`a : A → M`, a maximal compact subgroup `K` with `hK : IsIwasawaCompact p K`, a closed matrix
embedding `rho` and the smooth-structure data `hsmooth`, `hcalc`. No continuation of the
Eisenstein series enters.

Write `E(λ) = hK.eisensteinSeries φ λ`, and for a standard parabolic family `𝓕` and a standard
index `J` write `P_J = 𝓕.P J`, `𝔄_J = 𝓕.positiveSplitComponent J` and `a^ν` for
`parameterPower F P_J ν a`, so that `|a^ν| = e^{Re ν(H_J(a))}` with `H_J = characterLog`. The
conclusion: there are `b, n : ℕ` such that for every `𝓕` and every `J` there are

- a real `R`,
- a number `k ≤ b`,
- complex linear maps `L j : X^*(P) ⊗ ℂ → X^*(P_J) ⊗ ℂ` and parameters `c j ∈ X^*(P_J) ⊗ ℂ`
  for `j < k`,

such that:

1. *Subunitarity at unitary parameters.* For every `j`, every `x ∈ X^*(P) ⊗ ℝ` and every
   positive point `s` of `A_J` with `IsDominantSplitPoint J s`, with image
   `a = positivePointMap … s ∈ 𝔄_J`,
   `‖a^{L j (i x) + c j}‖ ≤ ‖𝓕.halfModulus J a‖ = δ_{P_J}(a)^{1/2}`.
2. *Expansion at regular parameters.* For every `λ` with `r.IsRegularParameter hA hT R λ` there
   are functions `f j : G(𝔸) → ℂ` with `𝓕.HasPolynomialOrbit J (L j λ + c j) n (f j)` for every
   `j` and `𝓕.constantTerm J (E(λ)) = ∑_j f j`.

`HasPolynomialOrbit J ν n f` says: for every `g` there is a complex polynomial function `q` of
degree at most `n` on `𝔞_J = Hom(X^*(P_J), ℝ)` with `f(a g) a^{-ν} = q(H_J(a))` for every
`a ∈ 𝔄_J`. So `ν = L j λ + c j` is an *unnormalized* exponent; the normalized exponent of the
sources is `ν − ρ_J`, where `ρ_J = halfModulusParameter F P_J` and
`a^{ρ_J} = 𝓕.halfModulus J a = δ_{P_J}(a)^{1/2}`.

The numbers `b` and `n` depend on the data of `P` and `φ` only. The threshold `R`, the number
`k` and the labels may depend on `𝓕` and `J`. The labels do not depend on `λ`, and the bound of
item 1 is asked for every unitary parameter `i x`, not only for regular ones.

## Correspondence with the sources

- *Subunitarity.* The positive point `s` is dominant when `|α(s)| ≥ 1` for every simple root
  `α ∉ J`, that is when `H_J(a)` lies in the closed chamber `𝔞_J^+` of Delorme §2. Since
  `|a^{ν}| / δ_{P_J}(a)^{1/2} = e^{Re(ν − ρ_J)(H_J(a))}` and `H_J : 𝔄_J → 𝔞_J` is onto, item 1
  says that the normalized exponent `L j (i x) + c j − ρ_J` is subunitary in Delorme's sense
  for every `x`.
- *Labels.* In the sources the exponents of the constant term along `Q = P_J` are
  `(wλ)|_{𝔞_Q}` for the leading terms `w ∈ Ω(P; Q)` and `[w(μ + λ)]_Q` with
  `μ ∈ E_{P_w}(φ)` for the remainder (normalized). Each is the value at `λ` of the affine map
  `λ ↦ [wλ]_Q + [wμ]_Q`; its linear part is the complex linear map `L j` and its constant part
  plus `ρ_Q` is `c j`. The statement keeps only this affine shape, not the formula for `L j`
  and `c j`.
- *Counts and degrees.* `k` counts the pairs `(w, μ)` (with `μ = 0` for the leading terms) and
  `n` bounds the degrees of the polynomial parts. Delorme's (4.4) records that these
  multiplicities depend only on those of the exponents of `φ`; the uniform bounds `b` and `n`
  express this. Several labels may coincide at a given `λ`; the statement does not merge them.
- *Families.* The sources fix a minimal parabolic `P_0`, take `P` standard and `K` in good
  position. Here `P`, `K` and the family `𝓕` are arbitrary, and `b`, `n` must serve all
  families. This is derived as in items 1 and 2 of "Why it is true" in
  `AdelicEisensteinUnitaryExponentStatement.md`.

## Why it is true

The following outline explains the statement; it is not proved here. Write `Q = P_J`.

1. *Families and standard position.* Two standard parabolic families are conjugate under
   `G(F)`, and by left `G(F)`-invariance of `E(λ)` the constant term along `γ Q γ⁻¹` is
   `g ↦ E(λ)_Q(γ⁻¹ g)`, with the split components and half moduli corresponding under
   conjugation by `γ`. So it suffices to treat one family. The Library's
   `eisensteinStandardization` (module `Langlands.Global.AdelicEisensteinStandardizationProof`)
   writes `E(λ)(g t)`, for an archimedean `t` and sufficiently regular `λ`, as a finite sum
   `∑_i exp(ℓ_i λ) E'(φ'_i, ιλ)(g)` of Eisenstein series for a standard parabolic of one
   standard family and a compact subgroup in good position, with linear forms `ℓ_i` and a
   linear isomorphism `ι` of parameter spaces. Constant terms commute with right translation,
   and terms with the same label combine into one term with that label, so `b` and `n` do not
   grow with the number of summands.
2. *Constant-term formula.* The Library's `eisensteinConstantTerm` (module
   `Langlands.Global.AdelicEisensteinConstantTermProof`) proves the formula of Lapid's
   Proposition 4 in the form of Bernstein–Lapid (6.17) for sufficiently regular `λ`.
3. *Leading terms.* For `w ∈ Ω(P; Q)` the split component `A_Q` lies in `w A_P w⁻¹` and is
   central in `M_Q`, so `a ∈ 𝔄_Q` acts on the summand by the character `a^{(wλ)|_Q + ρ_Q}`:
   one label with `n = 0`. For unitary `λ`, `|a^{(wλ)|_Q + ρ_Q}| = a^{ρ_Q}`.
4. *Remainder.* For `w ∈ _QΩ_P \ Ω(P; Q)`, decompose `φ_{P_w}` into its exponent components
   along `A_{P_w}` (Mœglin–Waldspurger I.3). The Library states this decomposition as
   `AutomorphicExponentDecompositionStatement` and derives it from Harish-Chandra's finiteness
   theorem `ParabolicHarishChandraFinitenessStatement`
   (`automorphicExponentDecomposition_of_parabolicHarishChandraFiniteness`). Each component
   with normalized exponent `μ` and polynomial part of degree `d`
   contributes, along `𝔄_Q`, a polynomial-exponential term with normalized exponent
   `[w(μ + λ)]_Q` and degree at most `d` (Lapid (13) with `R = Q`).
5. *Subunitarity.* For unitary `λ`, `Re[w(μ + λ)]_Q = [w Re μ]_Q`. Lapid's Lemma 6 gives
   `Re⟨wμ, ϖ^∨⟩ ≤ 0` for `ϖ ∈ Δ̂_{Q_w}`, which contains `Δ̂_Q`, and `wμ` vanishes on `𝔞_G`;
   so `[wμ]_Q` is subunitary on `𝔞_Q^+`.

## Use

With the root-hyperplane form of the continued Eisenstein series
(`EisensteinJointRootHyperplaneStatement`), this statement implies
`EisensteinUnitaryExponentStatement`: the polynomial orbits give difference equations along
`𝔄_J` with roots `a^{L j λ + c j}`, each repeated `n + 1` times; these roots are entire in `λ`,
so the equations extend from the regular region to the unitary parameters by meromorphic
continuation, and item 1 bounds the roots there.

## Scope

The statement asserts nothing about the continued Eisenstein series, nothing at non-regular
parameters except the bound of item 1 on the labels, and no formula for the labels or the
functions `f j`. Nothing is proved here.
