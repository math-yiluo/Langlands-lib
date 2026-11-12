# The inner product on `A^2_P`, measures on `𝔞_P` and `i𝔞_P^*`, and `Ω(P, Q)`

Module `Langlands.Global.AdelicInducedInnerProduct` defines the data that
Lapid's inner product formula for wave packets needs beyond `A^2_P`:
coordinates on `𝔞_P` dual to a basis of `𝔞_P^*`, the measure `dλ` on
`i𝔞_P^*`, the compatibility of a Haar measure on `M(𝔸)` with the Iwasawa
decomposition, the inner product `(·,·)_P`, the real form of the Weyl
action on parameters, and the Weyl set `Ω(P, Q)`. It is a definition module
and proves nothing.

## Source

E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series*, in: On Certain L-Functions, Clay Math. Proc. 13 (2011),
pp. 309–331, registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein` (volume PDF; PDF
page = printed page + 9).

- §2, p.311: Haar measures on `G(𝔸)`, `M(𝔸)`, `U(𝔸)`, `K` and `𝔞_P` are
  chosen compatibly with the Iwasawa decomposition. The norm on `A^2_P` is
  `‖φ‖²_P = ∫_{A_M P U(𝔸) \ G(𝔸)} |φ(g)|² dg`, with inner product `(·,·)_P`.
  The sets `Ω(P, Q)` are as in Arthur [Art80].
- §3, p.314: `‖φ‖²_* = ∫_{i𝔞_P^*} ‖φ(λ)‖²_P dλ` (formula (3)), the wave
  packets `Θ_{P,φ}` and Proposition 2, which use these measures.

Mœglin–Waldspurger I.1.13 (registered as
`moeglin-waldspurger-1995-spectral-decomposition`, chapter file
`05.1_pp_1_18_Hypotheses_and_general_notation.pdf`, printed p.18):
`meas(K) = 1`, `meas(U(F) \ U(𝔸)) = 1`, and the compatibility formula
`∫_G f(g) dg = ∫_{U(𝔸) × M × K} f(umk) m^{-2ρ_P} dk dm du`. MW I.1.13 also
gives `i𝔞_M^*` the measure for which `Re 𝔞_M^* → i𝔞_M^*` (via the
exponential) locally preserves measures; Lapid's `dλ` is instead dual to the
measure on `𝔞_P`, as below.

Getz–Hahn §10.2, p.273 (registered as
`getz-hahn-2024-automorphic-representations`; PDF page 285):
`W(𝔞_M, 𝔞_{M'})` is the set of linear isomorphisms `𝔞_M → 𝔞_{M'}` obtained by
restricting elements of the Weyl group `W(G, T)(F)`; this is Arthur's
`Ω(𝔞_P, 𝔞_{P'})`. The proof of their Lemma 10.2.1 (pp.273–274) shows that
if `gMg⁻¹ = M'` with `g ∈ G(F)`, then `mg` normalizes `T` for some
`m ∈ M'(F)`.

## Existing objects used

- `realParameterPairing F P : X^*(P) ⊗ ℝ → Hom(Hom(X^*(P), ℝ), ℝ)` and
  `characterLog F P` (modules `Langlands.Global.AdelicComplexParameters`,
  `Langlands.Global.AdelicCharacterLog`): `⟨χ, log_P(m)⟩ = log |χ(m)|_𝔸`, so
  `log_P` restricted to `M(𝔸)` (through `l`) is the map `H_M`.
- `modulusParameter F P`, `parameterPower` (module
  `Langlands.Global.AdelicSquareIntegrableInducedForms` and
  `AdelicComplexParameters`): `m^{-2ρ_P}`, which is `δ_P(m)⁻¹`.
- `AdelicSubgroupPoints.normalizedHaarMeasure F G H` (module
  `Langlands.Global.AdelicSubgroupHaarMeasure`): Haar measure on the adelic
  points of a closed subgroup `H`, multiplied by the inverse of the volume of
  `H(F) \ H(𝔸)` for the unnormalized quotient measure.
- `compactHaarProbability F G K hK` (module
  `Langlands.Global.AdelicParabolicModulus`).
- `LeftCosetSpace.discreteQuotientMeasure` (module
  `Langlands.Global.LeftCosetFundamentalDomain`) and `RationalQuotient F M`:
  the quotient measure on `M(F) \ M(𝔸)` of a measure on `M(𝔸)`, through a
  Borel fundamental domain for the discrete subgroup `M(F)`.
- `weylParameter l c π'` and `IsWeylConjugation p l q l' w c` (module
  `Langlands.Global.AdelicIntertwiningOperator`).

## Definitions

Namespace `Langlands.Global.AdelicGroupPoints`.

- `parameterCoordinates F P e H`, for a real linear isomorphism
  `e : ℝⁿ ≃ X^*(P) ⊗ ℝ` and `H ∈ Hom(X^*(P), ℝ)`, is the vector
  `y ∈ ℝⁿ` with `y_j = ⟨e(b_j), H⟩` (`b_j` the standard basis). Then
  `⟨e(x), H⟩ = ∑_j x_j y_j`.
- `spectralMeasure n = (2π)^{-n} · volume` on `ℝⁿ`.
- `IsIwasawaCompatibleMeasure K hKc p iU l μM`, for a measure `μM` on
  `M(𝔸)`: for every compactly supported continuous `f : G(𝔸) → ℂ`,
  `∫_{G(𝔸)} f d(haar) = ∫_K ∫_{M(𝔸)} ∫_{U(𝔸)} m^{-2ρ_P} f(u m k) du dμM(m) dk`,
  where `haar` is Mathlib's `Measure.haar` on `G(𝔸)`, `du` is
  `normalizedHaarMeasure` for the image of `U` in `G`, and `dk` is
  `compactHaarProbability`.
- `inducedInnerProduct K hKc p l μM e β φ ψ` is
  `∫_K ∫_{M(F) \ M(𝔸)} β(y(m)) m^{-2ρ_P} φ(m k) conj(ψ(m k)) dm dk`, where
  `m` is the chosen representative `x.out` of `x ∈ M(F) \ M(𝔸)`,
  `y(m) = parameterCoordinates F P e (log_P(l(m)))`, `dm` is the quotient of
  `μM` by counting measure on `M(F)`, and `dk` is `compactHaarProbability`.
- `realWeylParameter l c π' : X^*(P) ⊗ ℝ → X^*(Q) ⊗ ℝ` sends `r ⊗ χ` to
  `r ⊗ (χ ∘ l ∘ c ∘ π')`, the real form of `weylParameter l c π'`.
- `weylParameterSet p l q l' π'` is the set of the linear maps
  `weylParameter l c π'` for all pairs `(w, c)` with
  `IsWeylConjugation p l q l' w c`.

## Correspondence with the source

- Compatible measures. MW construct `dg` from measures on `U₀(𝔸)`, `M₀` and
  `K` and deduce the compatibility formula for every standard parabolic.
  Here the measure on `G(𝔸)` is Mathlib's Haar measure, `du` and `dk` are
  MW's, and the predicate says that `μM` is MW's measure on `M(𝔸)` relative
  to this `dg`. Because Haar measures on `M(𝔸)` are unique up to a positive
  scalar and both sides are positive functionals, a compatible Haar measure
  exists exactly when the formula holds up to a positive constant; that is
  the published (unproved) `AdelicIwasawaIntegrationStatement`
  (Mœglin–Waldspurger I.1.13). This is explanatory and not proved here.
- `δ_P`. `m^{-2ρ_P} = δ_P(m)⁻¹`, as explained in the Markdown of
  `Langlands.Global.AdelicSquareIntegrableInducedForms`.
- The inner product. Lapid's `(φ, ψ)_P` is the integral over
  `A_M U(𝔸) M(F) \ G(𝔸)`. In Iwasawa coordinates it is
  `∫_K ∫_{A_M M(F) \ M(𝔸)} δ_P(m)⁻¹ φ(mk) conj ψ(mk) dm dk`, with the
  quotient of `μM` by the chosen Haar measure on `A_M ≅ 𝔞_P`. For
  `φ, ψ ∈ A^n_P` the function `f(m) = δ_P(m)⁻¹ φ(mk) conj ψ(mk)` is left
  invariant under `M(F)` and `A_M`. Disintegrating `dm` on `M(F) \ M(𝔸)`
  along `H_M` gives
  `∫_{M(F) \ M(𝔸)} β(y(m)) f(m) dm = (∫_{A_M M(F) \ M(𝔸)} f) · ∫_{𝔞_P} β(y(H)) dH`.
  When `∫_{ℝⁿ} β = 1` for Lebesgue measure `dy`, the weight reduces to the
  ratio of `dH` to `dy`, and the definition is Lapid's inner product for the
  measure `dy` on `𝔞_P` (Lebesgue measure in the coordinates `y`). In
  particular it does not depend on `β` among such weights. The weight
  replaces an integral over the quotient `A_M M(F) \ M(𝔸)`, so no measure on
  `A_M` or on that quotient has to be chosen. These facts are explanatory and
  not proved here; the statements that use the definition assume `β`
  continuous, compactly supported and of integral `1`.
- Dual measures. Write `λ = i e(x)` on `i𝔞_P^*` and `y` for the coordinates
  of `H ∈ 𝔞_P`. Then `e^{⟨λ, H⟩} = e^{i x·y}`, and by the Fourier inversion
  formula on `ℝⁿ`, `(2π)^{-n} dx` is the measure dual to `dy`. So
  `spectralMeasure n` in the coordinates `x` is Lapid's `dλ` when `𝔞_P`
  carries `dy`. Changing `e` rescales `dy` and `dλ` inversely; the formulas
  in which both appear do not change. This is explanatory.
- `Ω(P, Q)`. `weylParameter l c π'` is the isomorphism
  `X^*(P) ⊗ ℂ → X^*(Q) ⊗ ℂ` induced by `w` (see the Markdown of
  `AdelicIntertwiningOperator`), the complexification of the source's
  `𝔞_P^* → 𝔞_Q^*`. An element of `W(G, T)(F)` mapping `𝔞_M` onto `𝔞_{M'}`
  conjugates `M`, the centralizer of its split centre, to `M'`; conversely,
  by the proof of Getz–Hahn's Lemma 10.2.1, `g ∈ G(F)` with `gMg⁻¹ = M'`
  induces the same map on `𝔞_M` as an element `mg` of `N_G(T)(F)`, because
  `m ∈ M'(F)` acts trivially on `𝔞_{M'}`. So `weylParameterSet` is
  Getz–Hahn's `W(𝔞_M, 𝔞_{M'})`, that is, Arthur's and Lapid's `Ω(P, Q)`,
  as a set of maps on complex parameters (dualized and complexified). It does not depend on the retraction `π'`, because characters
  of `Q` are trivial on its unipotent radical. This is explanatory.

## Scope

No statement about these objects is made here: convergence of the inner
product, its independence of `β`, the existence of compatible measures and
the finiteness of `Ω(P, Q)` are not asserted. The definitions take arbitrary
`p`, `iU`, `l`, `K` and measures.
