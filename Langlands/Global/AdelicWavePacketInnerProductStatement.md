# Square integrability and inner products of wave packets

Module `Langlands.Global.AdelicWavePacketInnerProductStatement` states
`Langlands.Global.WavePacketInnerProductStatement` as a proposition
definition. It supplies no proof.

## Source

E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series*, in: On Certain L-Functions, Clay Math. Proc. 13 (2011),
pp. 309–331, registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein` (volume PDF; PDF
page = printed page + 9).

- §3, p.314 (PDF page 323): `W_P` is the space of compactly supported smooth
  functions on `i𝔞_P^*` with values in a finite-dimensional subspace of
  `A^2_P` such that `E_P(·, φ(λ), λ)` is smooth on `i𝔞_P^*` ("Ultimately, the
  last condition is redundant"). For `φ ∈ W_P`,
  `Θ_{P,φ}(g) = ∫_{i𝔞_P^*} E_P(g, φ(λ), λ) dλ`.
- Proposition 2, p.314: for any `φ ∈ W_P`, `Θ_{P,φ} ∈ L²(G \ G(𝔸))`, and for
  any `φ' ∈ W_{P'}`, formula (4):
  `(Θ_{P,φ}, Θ_{P',φ'})_{G \ G(𝔸)} = ∫_{i𝔞_P^*} ∑_{w ∈ Ω(P, P')} (M(w, λ)φ(λ), φ'(wλ))_{P'} dλ`.
- §2, pp.311–312: `A^2_P`, `(·,·)_P`, compatible Haar measures, `Ω(P, Q)`,
  the intertwining operators `M(w, λ) : A_P → A_Q`, and the Working
  hypothesis: `M(w, λ)φ` takes values in a finite-dimensional subspace of
  `A^2_Q`, and for `λ ∈ i𝔞_P^*` it is unitary, hence holomorphic.

## Statement

The data, for a number field `F : Type`:

- `G` connected reductive; `P = MU` and `P' = M'U'` with presentations
  `r : ParabolicRootPresentation p l a` and
  `r' : ParabolicRootPresentation p' l' a'`, `p`, `p'`, `iU ≫ p` and
  `iU' ≫ p'` closed immersions, `iU`, `iU'` geometric unipotent radicals, all
  groups affine, `M` and `M'` locally of finite type (`P` and `P'` are
  locally of finite type as closed subgroups, supplied by `haveI`), and a
  Levi projection `π' : P' → M'` with `l' ≫ π' = 𝟙`;
- `K` maximal compact with `P(𝔸)K = P'(𝔸)K = G(𝔸)`, a closed matrix
  embedding `rho`, and the smooth-structure data `hsmooth`, `hcalc`;
- a Haar measure `μM'` on `M'(𝔸)` with
  `IsIwasawaCompatibleMeasure K hK'.isCompact p' iU' l' μM'` (module
  `Langlands.Global.AdelicInducedInnerProduct`);
- linear isomorphisms `e : ℝⁿ ≃ X^*(P) ⊗ ℝ`, `e' : ℝ^{n'} ≃ X^*(P') ⊗ ℝ` and
  a continuous compactly supported `β' : ℝ^{n'} → ℝ` with `∫ β' = 1`;
- the wave packet data of `P`: `v : Fin k → (G(𝔸) → ℂ)` with every `v j` in
  `A^2_P` (`IsSquareIntegrableInducedForm`), smooth compactly supported
  `c j : ℝⁿ → ℂ`, and `E`, `D` with `i𝔞_P^* ⊆ D` (the range of
  `imaginaryParameter F P`), every `λ ↦ E j λ g` meromorphic with domain of
  holomorphy `D`, and `E j λ = hK.eisensteinSeries (v j) λ` for `Re λ`
  sufficiently regular;
- the same data `v'`, `c'`, `E'`, `D'` for `P'`;
- a finite type `T` with pairs `(w t, cw t)`, each
  `IsWeylConjugation p l p' l' (w t) (cw t)`, such that
  `t ↦ weylParameter l (cw t) π'` is injective with image
  `weylParameterSet p l p' l' π'`;
- for every `t` and `j`, functions `ψ t j i ∈ A^2_{P'}` (`i < m`) and
  coefficients `coeff t j i`, meromorphic with one domain `DM ⊇ i𝔞_P^*`,
  with `M(w t, λ)(v j) = ∑ i, coeff t j i λ • ψ t j i` for `Re λ`
  sufficiently regular (`hK.intertwiningOperator hK' iU l iU' (cw t) π' (w t)`).

Let `Θ(g) = ∫ ∑ j, c j x · E j (i e(x)) g d(spectralMeasure n)(x)` and
`Θ'` likewise, and let `μG` be the quotient of Mathlib's Haar measure on
`G(𝔸)` by counting measure on `G(F)`. The conclusion:

1. `y ↦ Θ(y.out)` and `y ↦ Θ'(y.out)` are in `L²(G(F) \ G(𝔸), μG)`
   (`MemLp … 2`);
2. `∫ Θ(y.out) · conj Θ'(y.out) dμG(y)` equals
   `∫ ∑ t, ∑ j, ∑ i, ∑ j', c j x · coeff t j i (i e(x)) · conj (c' j' (x'_t)) · (ψ t j i, v' j')_{P'} d(spectralMeasure n)(x)`,
   where `x'_t = e'⁻¹(w_t e(x))` (`realWeylParameter`) and
   `(·,·)_{P'} = inducedInnerProduct K hK'.isCompact p' l' μM' e' β'`.

## Correspondence with the source

- `W_P`. A compactly supported smooth function `φ` on `i𝔞_P^*` with values
  in a finite-dimensional subspace `V` of `A^2_P` is `∑ j, c j · v j` for a
  basis `v j` of `V` and smooth compactly supported coefficients `c j`, here
  written in the coordinates `λ = i e(x)`. Lapid's condition that
  `E_P(·, φ(λ), λ)` be smooth on `i𝔞_P^*` is replaced by the requirement that
  each `E(v j, ·)` be holomorphic near `i𝔞_P^*` (`i𝔞_P^* ⊆ D`). By Lapid's
  Proposition 6 (`EisensteinImaginaryAxisHolomorphyStatement`) this holds
  for every element of `A^2_P`, so the two spaces agree; Lapid himself notes
  that the condition is redundant. The continuations enter in universal
  form, as in the published Bernstein–Lapid statements: any data `(E, D)`
  agreeing with the Eisenstein series for `Re λ` sufficiently regular give
  the same values on `D`, as explained in the Markdown of
  `EisensteinFunctionalEquationStatement`. This is explanatory and not
  proved here.
- `Θ`. Since `E_P(g, φ, λ)` is linear in `φ`,
  `E_P(g, φ(λ), λ) = ∑ j, c j x · E(v j, λ)(g)`, and `spectralMeasure n` in
  the coordinates `x` is Lapid's `dλ` for the measure `dy` on `𝔞_P` (Markdown
  of `AdelicInducedInnerProduct`). So `Θ` is Lapid's `Θ_{P,φ}`.
- `L²(G \ G(𝔸))`. Lapid's `G \ G(𝔸)` is `G(F) \ G(𝔸)`, without dividing by
  `A_G`. `Θ` is left `G(F)`-invariant because each `E(v j, λ)` is, so
  `y ↦ Θ(y.out)` does not depend on representatives. The measure on
  `G(F) \ G(𝔸)` is the quotient of the Haar measure `dg` to which `μM'` is
  compatible, as in Lapid's choice of compatible measures.
- The right side of (4). `Ω(P, P')` is enumerated once by `T`:
  `weylParameterSet` is `Ω(P, P')` (Markdown of `AdelicInducedInnerProduct`),
  and `M(w, λ)` depends only on the element of `Ω(P, P')`: two `w` inducing
  the same map differ by an element of `N_G(M)(F)` acting trivially on
  `𝔞_M`, that is, of `M(F)`, and right multiplication of `w` by `M(F)` does
  not change the intertwining integral of a left `P(F)`-invariant `φ_λ`. For
  `λ = i e(x)`, `M(w, λ)φ(λ) = ∑ j, c j x · ∑ i, coeff t j i λ · ψ t j i`,
  where on `i𝔞_P^*` the coefficients are the values of the continuation;
  such data exist because `M(w, λ)(v j)` takes values in a
  finite-dimensional subspace of `A^2_{P'}` and is holomorphic on `i𝔞_P^*`
  (Lapid p.312; Bernstein–Lapid 2.3 (3) and
  `IntertwiningMeromorphicContinuationStatement`). Since
  `w(i e(x)) = i e'(x'_t)` with `x'_t = e'⁻¹(w e(x))`,
  `φ'(wλ) = ∑ j', c' j' (x'_t) · v' j'`. Expanding the sesquilinear
  `(·,·)_{P'}` gives the integrand. This is explanatory.
- Normalization of `M(w, λ)`. Lapid's displayed integral on p.312 omits the
  factor `e^{-⟨wλ, H_Q(g)⟩}`, but his `M(w, λ)` maps `A_P` to `A_Q`, is
  unitary for `λ ∈ i𝔞_P^*`, and satisfies
  `E_Q(M(w, λ)φ, wλ) = E(φ, λ)`; this is Bernstein–Lapid's normalization
  `[M(w, λ)φ]_{wλ} = ∫ φ_λ(w⁻¹ v g) dv`, the Library's
  `IsIwasawaCompact.intertwiningOperator`.
- Measures. Lapid fixes compatible Haar measures on `G(𝔸)`, `M(𝔸)`, `U(𝔸)`,
  `K` and `𝔞_P`, and `dλ` dual to the measure on `𝔞_P`. Here `dg` is
  Mathlib's Haar measure, `μM'` is compatible with it, `𝔞_P` and `𝔞_{P'}`
  carry Lebesgue measure in the coordinates dual to `e` and `e'`, and the
  spectral measures are their duals. Changing `e` multiplies `Θ` and the
  measure on the right by the same factor; changing `e'` multiplies `Θ'` and
  `(·,·)_{P'}` by the same factor. So no relation between `e` and `e'` is
  needed, and no measure on `M(𝔸)` enters for `P`. This is explanatory.
- Regions and parabolics. "`Re λ` sufficiently regular" is
  `r.IsRegularParameter hA hT R λ` for some `R` (and `r'` for `P'`), as in
  the Markdown of `EisensteinAbsoluteConvergenceStatement`. Lapid takes `P`
  and `P'` standard for one minimal parabolic; here `r` and `r'` may use
  different ones, and a rational conjugation reduces the general case to
  his, as in the Markdown of `IntertwiningMeromorphicContinuationStatement`.
- The compact subgroup. Lapid fixes `K` in good position; here `K` is any
  maximal compact subgroup with `P(𝔸)K = P'(𝔸)K = G(𝔸)`. The reduction is
  the one described in the Markdown of
  `EisensteinAbsoluteConvergenceStatement`. This is explanatory and not
  proved here.
- Universe. `A^2_P` uses the canonical split component `A_M`, defined for
  `F : Type`.

## Scope

Lemma 10 (the extension to bounded measurable `φ`), Proposition 1, Theorem 1
and Theorem 2 (the isometry on the Hilbert space `L`) are not stated here.
The statement asserts square integrability of `Θ` and `Θ'` and formula (4);
the integrability of the right-hand integrand is not asserted separately.
