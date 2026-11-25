# Adjunction of continued intertwining operators

Module `Langlands.Global.AdelicIntertwiningAdjunctionStatement` states
`Langlands.Global.IntertwiningContinuedAdjunctionStatement` as a proposition
definition. It proves nothing. It is stated for
`IntertwiningImaginaryIsometryStatement`: the source proof of that statement
(Mœglin–Waldspurger IV.3.12) combines this adjunction with the functional
equation of intertwining operators.

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein
  series*, Cambridge Tracts in Math. 113 (1995), registered as
  `moeglin-waldspurger-1995-spectral-decomposition`:
  - II.1.8, "Adjunction of intertwining operators", pp.93–94 (chapter file
    `06.1_pp_78_100_Definitions.pdf`): for `Re π` in the positive cone of
    absolute convergence, `⟨φ', M(w, π)φ⟩ = ⟨M(w⁻¹, -w π̄)φ', φ⟩`. The proof
    unfolds the integral over `U'(𝔸)M'(k)Z \ G` of `M(w, π)φ · φ̄'` to an
    integral over `(U'(k) ∩ wU(k)w⁻¹)M'(k)Z \ G`, substitutes `g' = wg` and
    refolds along `U(𝔸)`.
  - IV.1.9 (e), p.140 (chapter file `08.1_pp_135_141_The_results.pdf`): "The
    adjunction formula II.1.8 can be continued to an equality of meromorphic
    functions."
  - IV.3.12, p.161 (chapter file `08.3_pp_149_164_The_case_of_relative_rank_1.pdf`),
    which uses this adjunction together with the functional equation.
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, Clay Math. Proc. 13 (2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (PDF page =
  printed page + 9), §2, pp.311–312: in the setting of p.311 (standard
  parabolics, a maximal compact subgroup in good position), for `φ ∈ A^2_P`
  the continuation of `M(w, λ)φ` takes values in a finite-dimensional
  subspace of `A^2_Q` (p.312, Working hypothesis, "a consequence of
  Langlands' theory").

MW state II.1.8 for cuspidal data and standard parabolics; Lapid works with
the spaces `A^2_P` of the discrete spectrum. This statement is for `A^2_P`,
with the integrability of the right-hand pairing as a hypothesis (see
"Inner products" below).

## Statement

The data, for a number field `F : Type`:

- a connected reductive `G`; a parabolic `p : P → G` with geometric unipotent
  radical `iU`, rational Levi `l : M → P`, presentation
  `r : ParabolicRootPresentation p l a` and Levi retraction `π`
  (`l ≫ π = 𝟙 M`); a parabolic `p' : P' → G` with the same data `iU'`, `l'`,
  `r'`, `π'`. All groups are affine, `M`, `M'` locally of finite type, and
  `p`, `p'`, `iU ≫ p`, `iU' ≫ p'` closed immersions;
- `(w, cw)` with `IsWeylConjugation p l p' l' w cw`, presenting an element of
  `W(P, P')`, and `cw'` with `IsWeylConjugation p' l' p l w⁻¹ cw'`,
  presenting its inverse in `W(P', P)` (this forces `cw' = cw⁻¹`);
- `K` maximal compact with `P(𝔸)K = P'(𝔸)K = G(𝔸)`, a closed matrix
  embedding `rho` and the smooth-structure data `hsmooth`, `hcalc`;
- Haar measures `μM`, `μM'` compatible with the Iwasawa decompositions
  (`IsIwasawaCompatibleMeasure`), coordinates `e : ℝⁿ ≃ X^*(P) ⊗ ℝ` and
  `e' = w ∘ e` (`e' x = realWeylParameter l cw π' (e x)`), and continuous
  compactly supported weights `β`, `β'` of integral `1`. They define
  `(·,·)_P = inducedInnerProduct K hK.isCompact p l μM e β` and
  `(·,·)_{P'} = inducedInnerProduct K hK'.isCompact p' l' μM' e' β'`,
  exactly as in `IntertwiningImaginaryUnitarityStatement`;
- the forward data: `φ ∈ A^2_P`, functions `ψ i ∈ A^2_{P'}` (`i < k`) and
  coefficients `coeff i`, meromorphic in linear coordinates with one domain
  `D`, such that `M(w, λ)φ(g) = ∑ i, coeff i λ · ψ i g` for `Re λ`
  sufficiently regular (`r.IsRegularParameter hA hT R λ`), where `M(w, λ)` is
  `hK.intertwiningOperator hK' iU l iU' cw π' w`;
- the reverse data: functions `φ' i' ∈ A^2_{P'}` (`i' < m`), automorphic forms
  `χ x` on `U(𝔸)M(F) \ G(𝔸)` (`x < k'`, `IsAutomorphicFunctionOn` for
  `parabolicQuotientSubgroup F p iU l`) and coefficients `coeff' i' x` on
  `X^*(P') ⊗ ℂ`, meromorphic with one domain `D'`, such that
  `M(w⁻¹, ν)(φ' i')(g) = ∑ x, coeff' i' x ν · χ x g` for `Re ν` sufficiently
  regular (`r'.IsRegularParameter hA' hT' R ν`), where `M(w⁻¹, ν)` is
  `hK'.intertwiningOperator hK iU' l' iU cw' π w⁻¹`.

The conclusion: there is an open dense set `S ⊆ ℂⁿ` such that for every
`s ∈ S`, with `λ = realChart e s`, if `λ ∈ D` and
`ν = weylParameter l cw π' (realChart e (-conj s)) ∈ D'`, then for every
`c : Fin m → ℂ` such that, with `X = ∑ x, (∑ i', c i' · coeff' i' x ν) · χ x`,
the integrand `AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ X` of `(φ, X)_P` is
integrable on `K × M(F) \ M(𝔸)` (for the product of the Haar probability
measure on `K` and the quotient of `μM` by counting measure on `M(F)`),

`(∑ i, coeff i λ · ψ i, ∑ i', c i' · φ' i')_{P'} = (φ, X)_P`.

The inner-product module defines `AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ ψ`, the
function `(k, x) ↦ β(y(m)) m^{-2ρ_P} φ(m k) conj ψ(m k)` (`m = x.out`) on
`K × M(F) \ M(𝔸)` whose iterated integral is `inducedInnerProduct`
(`Langlands.Global.AdelicInducedInnerProduct`, definition at lines 78–90).

## Correspondence with the source

- Conjugation. `realChart e : ℂⁿ ≃ X^*(P) ⊗ ℂ` (module
  `Langlands.Global.AdelicIntertwiningImaginaryUnitarityReduction`) sends `z`
  to `∑ t, z t • e(b_t)` for the real basis `e(b_t)` of `X^*(P) ⊗ ℝ`. So the
  complex conjugate of `λ = realChart e s` is `realChart e (conj s)`, and
  `ν = w(-λ̄) = -wλ̄`, MW's parameter of `M(w⁻¹, ·)`; `weylParameter l cw π'`
  is the complex linear map `λ ↦ wλ`.
- The operators. By the hypotheses on the data,
  `λ ↦ ∑ i, coeff i λ · ψ i` is the meromorphic continuation of
  `M(w, λ)φ`, and `ν ↦ ∑ x, coeff' i' x ν · χ x` that of `M(w⁻¹, ν)(φ' i')`.
  The right-hand function is therefore `M(w⁻¹, -wλ̄)(∑ i', c i' · φ' i')` by
  linearity. The conclusion is MW's identity
  `(M(w, λ)φ, φ'')_{P'} = (φ, M(w⁻¹, -wλ̄)φ'')_P` for every `φ''` in the span
  of the `φ' i'`, that is, the adjunction on this finite-dimensional space.
- Meromorphic continuation and the domain. MW IV.1.9 (e) asserts the identity
  of meromorphic functions. Here it is required only for `s` in some open
  dense subset of `ℂⁿ` and in the two holomorphy domains; this is weaker than
  the identity at every point of `D ∩ {λ : -wλ̄ ∈ D'}`.
- Inner products. `inducedInnerProduct K hKc p l μM e β φ ψ` is the iterated
  Bochner integral `∫_K (∫_{M(F) \ M(𝔸)} AdelicGroupPoints.inducedInnerProductIntegrand … (k, x) dx) dk`.
  Each inner integral, and the outer one, is `0` when its integrand is not
  integrable. When the integrand is integrable on the product
  `K × M(F) \ M(𝔸)`, Fubini's theorem identifies the iterated integral with
  the product integral, and for functions in `A^n_P` with `∫ β = 1` this is
  Lapid's quotient integral over `A_M U(𝔸) M(F) \ G(𝔸)` (Markdown of
  `AdelicInducedInnerProduct`, explanatory there). Both pairings of the
  identity are of this kind:
  - on the left, both functions are finite combinations of forms in
    `A^2_{P'}`, and the integrand of a pair of forms in `A^2_{P'}` is
    integrable on the product (the published
    `InducedInnerProductIntegrableStatement`, proved as
    `inducedInnerProductIntegrable`; the presentation `r'` and the retraction
    `π'` supply its hypotheses);
  - on the right, the integrability of the integrand is the hypothesis of the
    conclusion. The statement makes no claim about the right-hand side when
    that product is not integrable. The individual products `φ · conj (χ x)`
    need not be integrable.
  Every function of the identity is in the corresponding `A^n` space, because
  `M(w, λ)` maps `A^n_P` to `A^n_{P'}` in the normalization of Bernstein–Lapid
  used by `intertwiningOperator` (`[M(w, λ)φ]_{wλ}` is the intertwining
  integral). The hypothesis `e' = w ∘ e` makes the measures on `𝔞_P` and
  `𝔞_{P'}` correspond under `w`, as in the Markdown of
  `IntertwiningImaginaryUnitarityStatement`.
- Measures in the unfolding. MW's proof uses `dg` on `G(𝔸)`, the Haar
  measures on `U(𝔸)` and `U'(𝔸)` with `vol(U(F) \ U(𝔸)) = vol(U'(F) \ U'(𝔸)) = 1`
  (the measures of the intertwining integrals) and the quotient measures on
  `U(𝔸) \ G(𝔸)` and `U'(𝔸) \ G(𝔸)` they induce; Iwasawa compatibility of `μM`
  and `μM'` with the same `dg` makes `(·,·)_P` and `(·,·)_{P'}` the
  corresponding quotient integrals whenever the products are integrable.
- Parabolics and `K`. MW take `P`, `P'` standard and `K` in good position.
  The unfolding argument uses only the Iwasawa decompositions
  `P(𝔸)K = P'(𝔸)K = G(𝔸)` that define the heights in `intertwiningOperator`
  and the measure normalizations above, so the statement is made for every
  such `K` and for presented parabolics, as
  `IntertwiningImaginaryUnitarityStatement` is. The integrability of the
  right-hand product, which identifies the right-hand side with the source
  pairing, is a hypothesis of the conclusion and is not derived from the
  square-integrability of continued values. (Lapid's Working hypothesis
  would give `M(w⁻¹, ν)(∑ i', c i' · φ' i') ∈ A^2_P`, hence this
  integrability, for standard parabolics and `K` in good position; Lapid
  states it only in that setting, and
  `IntertwiningSquareIntegrableExpansionStatement` treats its extension as an
  additional assumption. This explanation does not use that extension; a user
  of the statement discharges the hypothesis for the data at hand, as the
  reduction in `Langlands.Global.AdelicIntertwiningImaginaryIsometryReduction`
  does, where the right-hand function is a form in `A^2_P`.)

## Provenance

Internal formulation of MW II.1.8 and IV.1.9 (e) in the Library's
coordinates: continued operators are given by their finite meromorphic
expansions, as in `IntertwiningCocycleStatement` and
`IntertwiningImaginaryIsometryStatement`; the second argument ranges over the
span of a finite family with one common reverse expansion, so that no
linearity of `M(w⁻¹, ν)` and no stability of `A^2_{P'}` under finite sums has
to be invoked; `-λ̄` is written in the real chart of `e`; the identity is
required on an open dense set of parameters, and only where the right-hand
pairing is an absolutely convergent integral on `K × M(F) \ M(𝔸)`. The
definition `AdelicGroupPoints.inducedInnerProductIntegrand` is the integrand of the published
`inducedInnerProduct`, named so that the hypothesis can be stated.

## Scope

The statement does not assert the functional equation, holomorphy of any
operator, square-integrability of continued values, integrability of the
individual products `φ · conj (χ x)`, or the identity at points outside the
open dense set it provides or where the right-hand product is not integrable.
