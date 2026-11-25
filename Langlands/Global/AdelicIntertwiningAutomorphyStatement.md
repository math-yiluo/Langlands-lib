# Uniform automorphy of intertwining operators

Module `Langlands.Global.AdelicIntertwiningAutomorphyStatement` serves
`Langlands.Global.IntertwiningFiniteSpanStatement` (module
`Langlands.Global.AdelicIntertwiningContinuationReduction`), the Lemma of Bernstein–Lapid §8.2.

The module contains four `Prop`-valued definitions in the namespace `Langlands.Global` and no
theorems. It states facts about `M(w, λ)φ` that the proof of that Lemma uses. It proves none of
them.

- `IntertwiningUniformAutomorphyStatement` is the form used by the finite-span proof.
- `IntertwiningSmoothSlicesStatement`, `IntertwiningModerateGrowthStatement` and
  `IntertwiningUniformCenterIdealStatement` are its three analytic parts. Each is meant to be
  proved separately.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), 187–234, registered as
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`. Pages are journal pages of the
  registered PDF. Line numbers refer to the TeX file `1911.02342.tex` in the same folder.
  - §2.2, p. 191 (PDF p. 5; TeX lines 415–440). This section defines `𝒜_P` as the automorphic
    forms on `U(𝔸)M(F) \ G(𝔸)` in the sense of Mœglin–Waldspurger I.2.17, and sets
    `φ_λ(g) = φ(g) m_P(g)^λ`. "For any `w ∈ W(P, Q)`, the intertwining operator
    `M(w, λ) : 𝒜_P → 𝒜_Q` is defined by the formula
    `[M(w, λ)φ]_{wλ}(g) = ∫ φ_λ(w⁻¹ u g) du`". The integral is over
    `(wU_Pw⁻¹ ∩ U_Q)(𝔸) \ U_Q(𝔸)`, and it converges for `⟨Re λ, α^∨⟩ ≫ 0` (citing
    Mœglin–Waldspurger II.1.6).
  - (6.5), p. 201 (PDF p. 15; TeX lines 1242–1257). For `m ∈ M(𝔸)`, the function
    `δ_Q(wmw⁻¹)^{-1/2} (M(w, λ)φ)(wmw⁻¹g)` equals `m_Q(g)^{-wλ}` times the intertwining integral of
    `δ_P(m)^{-1/2} φ(m w⁻¹ u g) m_P(w⁻¹ug)^λ`.
  - §8.2, Lemma and proof, p. 222 (PDF p. 36; TeX lines 3274–3290). "For any `φ ∈ 𝒜_P` and
    `w ∈ W(P, Q)` the automorphic forms `M(w, λ)φ`, whenever defined, belong to a
    finite-dimensional linear subspace of `𝒜_Q` (independently of `λ`)." The proof takes a
    finite-codimensional ideal `I` of `𝔷^M` annihilating
    `m ↦ δ_P(m)^{-1/2} φ(mg)` for all `g`. By (6.5) the ideal `wI` of `𝔷^{M_Q}` annihilates
    `m ↦ δ_Q(m)^{-1/2} (M(w, λ)φ)(mg)` for all `g`. "It follows that there exists a
    finite-codimensional ideal of `𝔷` (independent of `λ`) that annihilates `M(w, λ)φ`".
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series*, Cambridge
  University Press, 1995, registered as `moeglin-waldspurger-1995-spectral-decomposition`.
  - II.1.6, Proposition (i), printed pp. 87–88 (chapter PDF `06.1_pp_78_100_Definitions.pdf`,
    pp. 10–11). The intertwining integral "converges absolutely and uniformly when `g` varies in a
    compact set" for `Re π` in the stated cone. It "defines an element of
    `A(U'(𝔸)M'(k) \ G)_{wπ}`", that is, an automorphic form on `V(𝔸)M'(F) \ G(𝔸)`. The Remark
    on p. 87 compares the two quotients `(V(F) ∩ wU(𝔸)w⁻¹) \ V(𝔸)` and
    `(V(𝔸) ∩ wU(𝔸)w⁻¹) \ V(𝔸)`.
  - I.2.17, printed pp. 37–39 (chapter PDF `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`,
    pp. 20–22). Automorphic forms on `U(𝔸)M(k) \ G` are defined there by moderate growth,
    smoothness, `K`-finiteness and `𝔷`-finiteness. The proof transfers `𝔷`-finiteness to the
    Levi through a homomorphism `𝔷 → 𝔷_M`. Page 39 notes that such forms and their derivatives
    have moderate growth.

## Common setting

Each of the four statements has exactly the binders and hypotheses of
`IntertwiningFiniteSpanStatement`, in the same order:

- a number field `F` and a connected reductive `G`;
- a parabolic `p : P → G` with unipotent radical `iU`, rational Levi `l : M → P` and presentation
  `r`;
- a parabolic `q : Q → G`, a closed immersion, with unipotent radical `iV`, rational Levi
  `l' : M' → Q` complementary to `iV`, and a retraction `π'` (`l' ≫ π' = 𝟙 M'`);
- a pair `(w, c)` with `IsWeylConjugation p l q l' w c`;
- a maximal compact `K` with `hK : IsIwasawaCompact p K` and `hK' : IsIwasawaCompact q K`;
- a closed matrix representation `rho`, the data `hsmooth` and `hcalc`;
- a function `φ` with `IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
  (K.comap (ofInfinite F G).toMonoidHom) rho φ`, i.e. `φ ∈ 𝒜_P`.

Write `T λ` for `hK.intertwiningOperator hK' iU l iV c π' w φ λ`. This is the Library's
`M(w, λ)φ = m_Q^{-wλ} · ∫ φ_λ(w⁻¹ v ·) dv` (module `Langlands.Global.AdelicIntertwiningOperator`).
The integral is over `(V(F) ∩ wU(𝔸)w⁻¹) \ V(𝔸)`, and the Haar measure on `V(𝔸)` gives
`V(F) \ V(𝔸)` volume `1`. The integral is set to `0` where the integrand is not integrable.
"`λ` is `R`-regular" means `r.IsRegularParameter hA hT R λ`: `R < B(Re λ|_A, α)` for every root
`α` of `A` in the unipotent radical of `P`. Regularity at `R` implies regularity at every
`R' ≤ R`. So conclusions of the form "there is `R₀` such that for every `R₀`-regular `λ` …" can
be combined by taking the largest of their thresholds. By the Library's
`intertwiningIntegrability`, for `λ` regular enough the integrand is integrable at every `g`. So
`T λ` is the actual intertwining integral there, and the totalization never applies.

Each statement concludes with the existence of a threshold `R₀` (and, in two of them, of an
ideal `J`) before the quantifier over `λ`. Nothing in the hypotheses depends on `λ`.

## The statements

### `IntertwiningUniformAutomorphyStatement`

There are `R₀ : ℝ` and an ideal `J` of `AdelicEnvelopingCenter F G hsmooth`, the center `𝔷` of the
complex enveloping algebra of the infinite adelic group, with:

1. `𝔷 / J` finite-dimensional over `ℂ`;
2. for every `R₀`-regular `λ`:
   - `IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F q iV l')
     (K.comap (ofInfinite F G).toMonoidHom) rho (T λ)`. So `T λ` is left invariant under
     `V(𝔸)M'(F)`, smooth (continuous, plot-smooth infinite slices, fixed by an open subgroup of
     `G(𝔸_f)`), finite under the infinite part of `K`, `𝔷`-finite and of moderate growth for the
     norm of `rho`;
   - for every `z ∈ J`, every finite adelic point `b`, and every proof `h` that the infinite
     slice `functionInfiniteSlice F G (T λ) b` is plot-smooth,
     `plotSmoothCenterAction F G hsmooth hcalc z ⟨slice, h⟩ = 0`.

The last clause has the same form as the conclusion of `IsCenterFiniteFunction`, but `J` is
chosen before `λ`. `IsAutomorphicFunctionOn` alone gives an ideal for each `λ` separately. A
single ideal for all `λ` is what the §8.2 Lemma needs before Harish-Chandra's finiteness theorem
can bound the span. The clause is stated without a new definition, so that this module and
modules that name such a clause separately do not depend on each other.

This is Mœglin–Waldspurger II.1.6 (i) ("defines an element of `A(U'(𝔸)M'(k) \ G)`") together
with the uniform ideal from the proof of the Lemma in Bernstein–Lapid §8.2.

### `IntertwiningSmoothSlicesStatement`

There is `R₀` such that for every `R₀`-regular `λ` and every finite adelic point `b`,
`functionInfiniteSlice F G (T λ) b ∈ InfinitePlotSmoothFunctions F G`. This is the smoothness
in the infinite variable contained in "defines an element of `A(U'(𝔸)M'(k) \ G)`"
(Mœglin–Waldspurger II.1.6 (i), with I.2.17 (ii)).

### `IntertwiningModerateGrowthStatement`

There is `R₀` such that for every `R₀`-regular `λ`, `HasModerateGrowthFunction F G rho (T λ)`:
there are `C > 0` and a real `r` with `‖T λ g‖ ≤ C ‖g‖^r` for the adelic norm of `rho`. The
constants may depend on `λ`. This is the moderate growth contained in the same sentence of
Mœglin–Waldspurger II.1.6 (i), with I.2.17 (i).

### `IntertwiningUniformCenterIdealStatement`

There are `R₀` and an ideal `J` of `𝔷` of finite codimension such that for every `R₀`-regular
`λ`, every `z ∈ J` annihilates every plot-smooth infinite slice of `T λ`, in the same form as in
`IntertwiningUniformAutomorphyStatement`. This is the sentence "there exists a
finite-codimensional ideal of `𝔷` (independent of `λ`) that annihilates `M(w, λ)φ`" in the proof
of the Lemma in Bernstein–Lapid §8.2. If the slices are not plot-smooth the clause is vacuous.
It is meant to be used together with `IntertwiningSmoothSlicesStatement`.

## Why the statements hold

These are sketches of the source arguments, meant for whoever proves the statements. They are
not formalized here.

- **Smooth slices.** In the infinite variable the integrand is `v ↦ φ_λ(w⁻¹ v g)`, and right
  derivatives of `g ↦ φ_λ(w⁻¹ v g)` are the twisted integrands of right derivatives of `φ`
  (and of the height power). Those derivatives are again automorphic on `U(𝔸)M(F) \ G(𝔸)`.
  Mœglin–Waldspurger I.2.17 (p. 39) notes that automorphic forms and their derivatives have
  moderate growth. Differentiation under the integral sign then needs majorants of the kind in
  `IntertwiningAbsoluteConvergenceStatement` for all the derivatives together. The thresholds
  must be controlled uniformly in the order of differentiation, and this uniformity is the
  main point of the proof.
- **Moderate growth.** The proof of Mœglin–Waldspurger II.1.6 (i) (p. 88) bounds the integral
  by `∫_{V(F) \ V(𝔸)} Σ_{γ ∈ P(F) \ G(F)} |φ_λ(γ v g)| dv`. `V(F) \ V(𝔸)` is compact. The proof
  of Proposition II.1.5 (pp. 85–87) bounds the series of absolute values by a positive
  Eisenstein series, which converges and defines an automorphic form, hence has moderate growth.
  The factor `m_Q(g)^{-wλ}` also has moderate growth (compare Mœglin–Waldspurger I.2.2 (v),
  p. 20).
- **Uniform center ideal.** This is Bernstein–Lapid's argument quoted above. By
  Mœglin–Waldspurger I.2.17 there is an ideal `I` of finite codimension in `𝔷^M` annihilating the
  normalized Levi restrictions `m ↦ δ_P(m)^{-1/2} φ(mg)`. Twisting by `m_P^λ` shifts `I` by
  `λ`. By (6.5), conjugation by `w` carries the normalized source restrictions to the
  normalized restrictions of `[M(w, λ)φ]_{wλ}` to `M'`, so these are annihilated by the
  `wλ`-shift of `wI`. The factor `m_Q^{-wλ}` in `M(w, λ)φ` removes that shift. So `wI`
  annihilates the normalized Levi restrictions of `M(w, λ)φ` for every `λ`. The finite
  homomorphism `𝔷 → 𝔷^{M'}` of Mœglin–Waldspurger I.2.17 then gives an ideal of finite
  codimension in `𝔷`, independent of `λ`. This holds without assuming that `φ` lies in a single
  generalized eigenspace for the action of `A_P`, because the shifts cancel for each `λ`.

## What is not stated here

`IntertwiningUniformAutomorphyStatement` contains four further properties of `T λ`:

- left invariance under `V(𝔸)M'(F)`;
- continuity;
- finiteness under the infinite part of `K`;
- invariance under an open subgroup of `G(𝔸_f)`.

These follow from the definition of the operator, the convergence theorem
(`intertwiningAbsoluteConvergence`, `intertwiningIntegrability`) and the right `K`-invariance of
the Iwasawa heights. They are not stated here. The intended route derives
`IntertwiningUniformAutomorphyStatement` from the three analytic
statements and these four properties. Harish-Chandra's finiteness theorem then gives
`IntertwiningFiniteSpanStatement`.

## Provenance

The four statements are derived from the cited sources. The split into three analytic parts is
internal to this project. Each part is one of the defining conditions of an automorphic form
(Mœglin–Waldspurger I.2.17), asserted for `M(w, λ)φ` as in Mœglin–Waldspurger II.1.6 (i). The
center ideal is required to be uniform in `λ`, as in Bernstein–Lapid's proof of the §8.2 Lemma.
The statements use the Library's quotient `(V(F) ∩ wU(𝔸)w⁻¹) \ V(𝔸)` and its normalized
operator. The Remark in Mœglin–Waldspurger II.1.6 (p. 87) explains why integrating over this
quotient gives the same values as Bernstein–Lapid's integral over
`(V ∩ wUw⁻¹)(𝔸) \ V(𝔸)`.
