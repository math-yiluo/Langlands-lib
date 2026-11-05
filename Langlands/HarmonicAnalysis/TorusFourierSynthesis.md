# Fourier synthesis on a finite product of circles

Lean module: `Langlands.HarmonicAnalysis.TorusFourierSynthesis`, namespace
`Langlands.HarmonicAnalysis.TorusFourier`. It imports the published
`Langlands.HarmonicAnalysis.TorusFourierDecay` for the characters
`torusCharacter m z = ∏_j z_j^{m_j}` (`norm_torusCharacter`), the angle derivatives
`torusPartialDeriv j` and `torusPartialDeriv_finiteTorusExp`. Through it, it uses the published
`Langlands.Representation.Plancherel.RationalOrbitSmoothFunctions` for the real-angle covering
`finiteTorusExp θ = (e^{i θ_j})_j` of `J → Circle` (`isOpenQuotientMap_finiteTorusExp`) and the
smoothness predicate `IsSmoothFiniteTorusFunction f`, which means that `f ∘ finiteTorusExp` is
`C^∞` on `J → ℝ`. From Mathlib it uses `hasFDerivAt_integral_of_dominated_of_fderiv_le`
(`Mathlib.Analysis.Calculus.ParametricIntegral`), `contDiff_succ_iff_hasFDerivAt`,
`contDiff_infty`, `integral_finsetSum`, `ContinuousLinearMap.integral_comp_comm`,
`norm_integral_le_integral_norm` and `measurable_of_countable`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082,
Proposition VII.1.3 and its proof, printed pp. 316–317 (PDF pp. 82–83). After the reduction
to `M = G`, the proof sets, for `v ∈ E^H`, `v̌ ∈ Ě^H`, `f ∈ 𝒞_H`, `χ ∈ Im X(G)`,

> `C_{v⊗v̌,f}(χ) = d(ω ⊗ χ)⟨(ω ⊗ χ)(f̌)v, v̌⟩`

and states that the proposition follows from: "pour tout `f ∈ 𝒞_H`,
`C_{v⊗v̌,f} ∈ C^∞(Im X(G))`" and that `𝒞_H → C^∞(Im X(G))`, `f ↦ C_{v⊗v̌,f}` is continuous.
It continues: "Les propriétés ci-dessus résultent de la majoration suivante", namely the
estimate (2) for `∫_G |f̌(g)⟨ω(g)v, v̌⟩D(χ(g))| dg`, where `D` is a differential operator with
constant coefficients on `Im X(G)`.

Since `⟨(ω ⊗ χ)(f̌)v, v̌⟩ = ∫_G f̌(g) χ(g) ⟨ω(g)v, v̌⟩ dg`, the function `C_{v⊗v̌,f}` is, up to
the constant `d(ω)`, an integral over `G` of the characters `χ ↦ χ(g)` of `Im X(G)` against
`F(g) = f̌(g)⟨ω(g)v, v̌⟩`. Waldspurger does not write out why (2) gives smoothness and
continuity; the step is differentiation under the integral sign. This module proves that step
for a torus written in coordinates, `T = J → Circle` with `J` finite, and for an abstract
measure space in place of `G`. The proof is the standard dominated differentiation argument;
it is derived for this purpose and does not follow a cited text. The estimate (2) itself and
the application to `C(G)` are in
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.TwistedCoefficientSmoothness`.

## Scope and hypotheses

`J` is a finite type (`Fintype J`); `DecidableEq J` is assumed for the results that use
`torusPartialDeriv` (which uses `Pi.single`). `X` is a measurable space and `μ` an arbitrary
measure on `X`. The norm on `J → ℤ` is the sup norm, `‖m‖ = max_j |m_j|`. The map
`n : X → (J → ℤ)` abstracts the lattice coordinates: in the application `χ(g) = ∏_j z_j^{n(g)_j}`.

Not made here:

- the identification of Waldspurger's `Im X(G)` with `J → Circle` and of `χ(g)` with
  `torusCharacter (n g) z`;
- the general constant-coefficient operator `D`; the operators used are the iterated angle
  derivatives `∂_{j₁} ∘ ⋯ ∘ ∂_{jₖ}`, and every constant-coefficient operator on the torus is a
  linear combination of these.

Hypotheses of the results (`hn : Measurable n`, `hF : HasTorusMoments μ n F`):

- `angleForm_apply`, `norm_cexp_angleForm`, `torusCharacter_finiteTorusExp`,
  `norm_angleForm_le`, `smul_angleForm`, `torusSynthesis_comp_finiteTorusExp`,
  `torusSynthesis_const_mul`, `norm_list_prod_I_mul_le`, `norm_torusSynthesis_le`: none.
- `HasTorusMoments.integrable`: `hF`.
- `HasTorusMoments.mul_left`: `hn`, `hF`, and `hc : ∀ m, ‖c m‖ ≤ ‖m‖ ^ p` for the multiplier
  `c : (J → ℤ) → ℂ` and some `p : ℕ`.
- `integrable_mul_cexp_angleForm`, `HasTorusMoments.integrable_mul_torusCharacter`,
  `hasFDerivAt_torusSynthesis_comp`, `isSmoothFiniteTorusFunction_torusSynthesis`: `hn`, `hF`.
- `contDiff_torusSynthesis_comp`: `hn`; for every `k : ℕ` and every `F` with `hF`.
- `HasTorusMoments.add`, `torusSynthesis_add`: `hn`, `h₁ : HasTorusMoments μ n F₁`,
  `h₂ : HasTorusMoments μ n F₂`.
- `torusPartialDeriv_torusSynthesis`, `torusPartialDerivList_torusSynthesis`,
  `norm_torusPartialDerivList_torusSynthesis_le`: `DecidableEq J`, `hn`, `hF`.

## Definitions

- `angleForm m : (J → ℝ) →L[ℝ] ℂ`, the real linear form `θ ↦ i ∑_j m_j θ_j`.
- `torusSynthesis μ n F z = ∫ F(x) torusCharacter (n x) z dμ(x)`, the Fourier synthesis of
  `F` along `n`, a function on `J → Circle`. It is a Bochner integral, so it is `0` where the
  integrand is not integrable.
- `HasTorusMoments μ n F : Prop`: `F` is a.e. strongly measurable and
  `x ↦ ‖n(x)‖^k |F(x)|` is integrable for every `k : ℕ`.
- `torusPartialDerivList l f = l.foldr torusPartialDeriv f`, the composite
  `∂_{j₁} ∘ ⋯ ∘ ∂_{jₖ}` for `l = [j₁, …, jₖ]` (written `∂_l`).

## Results

- `angleForm_apply`: `angleForm m θ = (∑_j m_j θ_j) i`.
- `norm_cexp_angleForm`: `|e^{angleForm m θ}| = 1`.
- `torusCharacter_finiteTorusExp`: `χ_m(finiteTorusExp θ) = e^{angleForm m θ}`.
- `norm_angleForm_le`: `‖angleForm m‖ ≤ |J| ‖m‖`.
- `smul_angleForm`: `c • angleForm m = ∑_j (proj_j).smulRight (i m_j c)`.
- `torusSynthesis_comp_finiteTorusExp`: the angle lift of the synthesis is
  `θ ↦ ∫ F(x) e^{angleForm (n x) θ} dμ`.
- `HasTorusMoments.integrable`: `F` is integrable.
- `HasTorusMoments.mul_left`: `x ↦ c(n x) F(x)` has finite moments when `|c(m)| ≤ ‖m‖^p`.
- `integrable_mul_cexp_angleForm`, `HasTorusMoments.integrable_mul_torusCharacter`: the
  integrands of the synthesis (in angle and in torus form) are integrable.
- `HasTorusMoments.add`, `torusSynthesis_add`: finite moments and the synthesis are additive.
- `torusSynthesis_const_mul`: the synthesis of `c F` is `c` times the synthesis of `F`.
- `hasFDerivAt_torusSynthesis_comp` (**differentiation under the integral**): the angle lift
  of the synthesis has derivative `∑_j (proj_j).smulRight (Φ_j(finiteTorusExp θ₀))` at `θ₀`,
  where `Φ_j` is the synthesis of `x ↦ i n(x)_j F(x)`.
- `contDiff_torusSynthesis_comp`: the angle lift is `C^k` for every `k : ℕ`.
- `isSmoothFiniteTorusFunction_torusSynthesis`: the synthesis is smooth on the torus.
- `torusPartialDeriv_torusSynthesis`: `∂_j` of the synthesis of `F` is the synthesis of
  `x ↦ i n(x)_j F(x)`.
- `norm_list_prod_I_mul_le`: `|∏_{j ∈ l} i m_j| ≤ ‖m‖^{|l|}`.
- `torusPartialDerivList_torusSynthesis`: `∂_l` of the synthesis of `F` is the synthesis of
  `x ↦ (∏_{j ∈ l} i n(x)_j) F(x)`.
- `norm_torusSynthesis_le`: `|torusSynthesis μ n F z| ≤ ∫ |F| dμ` (both Bochner integrals).
- `norm_torusPartialDerivList_torusSynthesis_le`: `|∂_l Φ(z)| ≤ ∫ ‖n(x)‖^{|l|} |F(x)| dμ(x)`
  for all `z`, where `Φ` is the synthesis of `F`.

## Proof notes

1. `torusCharacter_finiteTorusExp`: `∏_j (e^{i θ_j})^{m_j} = ∏_j e^{i m_j θ_j} = e^{i ∑_j m_j θ_j}`
   (`Circle.exp_intCast_mul`, `Complex.exp_sum`). `norm_angleForm_le` bounds
   `|∑_j m_j θ_j| ≤ ∑_j ‖m‖ ‖θ‖`.
2. `hasFDerivAt_torusSynthesis_comp`: for fixed `x`, the integrand
   `θ ↦ F(x) e^{angleForm (n x) θ}` has derivative `F(x) e^{angleForm (n x) θ} • angleForm (n x)`,
   which `smul_angleForm` writes as `∑_j (proj_j).smulRight (i n(x)_j F(x) e^{…})`. Its norm is
   at most `|J| ‖n(x)‖ |F(x)|`, integrable by the first moment. The integrands are integrable
   because `|e^{angleForm …}| = 1`. `hasFDerivAt_integral_of_dominated_of_fderiv_le` then gives
   the derivative as the integral of the sum. `integral_finsetSum` splits the sum, and
   `integral_comp_comm` for the continuous linear map `smulRightL (proj_j)` moves each integral
   inside, giving `Φ_j(finiteTorusExp θ₀)`.
3. `contDiff_torusSynthesis_comp`: induction on `k`, for all `F` at once. The functions
   `i n_j F` have finite moments by `HasTorusMoments.mul_left` with `p = 1`, so by induction
   each `Φ_j ∘ finiteTorusExp` is `C^k`; the derivative from step 2 is a finite sum of
   `smulRight`s of these with constant forms, hence `C^k`, and `contDiff_succ_iff_hasFDerivAt`
   gives `C^{k+1}`. `contDiff_infty` gives smoothness.
4. `torusPartialDeriv_torusSynthesis`: every `z` is `finiteTorusExp θ`, and the published
   `torusPartialDeriv_finiteTorusExp` gives `∂_j Φ(finiteTorusExp θ) = D(Φ ∘ finiteTorusExp)(θ)(e_j)`;
   evaluating the derivative of step 2 at `e_j = Pi.single j 1` leaves the `j`-th term.
5. `torusPartialDerivList_torusSynthesis`: induction on `l`, using step 4 and
   `HasTorusMoments.mul_left` with the bound `norm_list_prod_I_mul_le`.
6. The bounds: `norm_integral_le_integral_norm` and `|χ_m(z)| = 1` give
   `norm_torusSynthesis_le`; with step 5 and `integral_mono` this gives
   `norm_torusPartialDerivList_torusSynthesis_le`.

## Relation to the Library

`TorusFourierDecay` treats the converse direction: Fourier coefficients of smooth functions on
`J → Circle` decay rapidly. `TorusFourierAveraging` averages a function over a torus of twists
(`torusAverage`, the `ϕ_g` of the proof of Proposition VI.3.1) and bounds it by that decay. `Langlands.Analysis.CompactLinearParameterIntegralProof` differentiates integrals
over a compact set of a smooth function of a linear parameter with continuous coefficients; it
does not cover integrals over a non-compact measure space with moment conditions, which is the
case here. A search of the Library for `hasFDerivAt_integral_of_dominated` and
`IsSmoothFiniteTorusFunction` found no Fourier synthesis on the torus.

## Open obligations

Applying this to Proposition VII.1.3 requires the identifications listed as not made under
Scope, the coefficient estimate (2), which is proved in `TwistedCoefficientSmoothness` for
`F = f φ` with `f ∈ C(G)`, and the reduction to `M = G` through Lemma VII.1.2.
