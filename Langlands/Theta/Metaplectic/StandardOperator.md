# The standard Weil operator of a polarization

**GKT §2.3.1** (the operators `M_X(g)` (2.10), the standard Weil operator `r(g)` (2.12),
**Definition 2.9**, the section `s_r`, p. 53–54; `ker(c) = gX ∩ X` (2.15) and (2.16), p. 55;
**Proposition 2.13** and (2.17), p. 55; the c-part, Definition 2.15 and (2.18), p. 56), with
Proposition 2.5 (p. 51) through the restriction `R_{X,Y}` of Theorem 1.13 (p. 25).

The module `Langlands.Theta.Metaplectic.StandardOperator` defines, for every isometry `g` of the
polarized space `(X × Y, polarizedForm β)`, the standard Weil operator `r(g)` on the Schrödinger
model `S(X)`, with its measure `d_g` fixed by unitarity, and shows that `(g, r(g))` lies in the
metaplectic group of pairs.

## Content

Let `F` be a nonarchimedean local field with `2 ≠ 0`, `β : X →ₗ[F] Y →ₗ[F] F` a perfect pairing of
finite-dimensional spaces with their module topologies, and `ψ` a continuous non-trivial
character. In the book's notation `W = X_B ⊕ Y_B` with `X_B = 0 × Y`, `Y_B = X × 0`,
`⟨y_B, x_B⟩ = β(y_B, x_B)`.

**Blocks.** For `g` in `isometryGroup (polarizedForm β)` write `g⁻¹ (x, y) = (d x + c y, b x + a y)`
(`isometryInv_apply_eq`): this is the book's `g⁻¹ = [[a, b], [c, d]]` with respect to `X_B ⊕ Y_B`.
`standardC g = c` is the c-part of `g⁻¹` (Definition 2.15, (2.18)); `standardD`, `standardB`,
`standardA` are the other blocks, related by `β(d x, a y) − β(c y, b x) = β(x, y)`
(`pairing_standardD_standardA`, from `g` being an isometry). `standardKernel g = ker c` is the
book's `gX ∩ X` ((2.15)).

**The integrand.** `standardIntegrand ψ g φ x y = ψ(½ β(x', y') − ½ β(x, y)) φ(x')`,
`(x', y') = g⁻¹ (x, y)`: the induced function `f_φ` of Theorem 1.13 at `g⁻¹ · ((0, y)(x, 0))`, so that
integrating it over `y` is (2.10) read through `R_{X,Y}`. Properties:

- `standardIntegrand_add_kernel`: invariance under `ker c` (on `ker c`, `β(x', a k) = β(x, k)`,
  `pairing_isometryInv_kernel`);
- `standardIntegrand_eq`: **(2.17)**, the integrand is
  `ψ(½ β(dx, bx)) ψ(β(cy, bx) + ½ β(cy, ay)) φ(cy + dx)` (re-derived; the book's statement
  `ψ(⟨cx, by + ½ ax⟩)` and the last line of its proof `ψ(⟨cx, by⟩ − ½⟨ax, cx⟩)` agree);
- `standardIntegrand_schrodinger`: the integrand of `σ(h) φ` at `(x, y)` is
  `ψ(t + β(x, y₁) + ½ β(x₁, y₁))` times the integrand of `φ` at `(x + x₁, y + y₁)`, where
  `((x₁, y₁), t) = g · h` (an identity of phases, from the isometry property of `g⁻¹`).

**The operator for a Haar measure.** `standardIntegrandQ` is the integrand on the quotient
`Y ⧸ ker c` (the book's `ker(c) \ X`), `standardOperatorFun ψ g μ φ x = ∫ standardIntegrandQ dμ`.

- `continuous_standardIntegrandQ`, `hasCompactSupport_standardIntegrandQ` (the induced
  `c̄ : Y ⧸ ker c → X`, `standardCQ`, is injective, `standardCQ_injective`, and the integrand
  vanishes unless `c̄ q` lies in a translate of the support of `φ`), `integrable_standardIntegrandQ`.
- `standardOperatorFun_schrodinger`: **`r_μ(g) ∘ σ(h) = σ(g · h) ∘ r_μ(g)`** on all functions
  (Proposition 2.5 in the Schrödinger model), from the shift identity and the invariance of `μ`.
- `standardOperatorFun_mem`: `r_μ(g)` preserves `S(X)`: the output is fixed by `σ(g · h)` for `h` in
  an open subgroup fixing `φ` (`isSmooth_schrodingerSB`); invariance under small translations makes
  it locally constant, invariance under the multiplications `ψ(β(·, y))`, `y` small, confines it to
  a compact set (`isPerfectBicharacter_pairing`, `IsPerfectBicharacter.big_right`).
- `standardOperatorWith hψ hψ1 g μ`, the linear map of `S(X)`; `standardOperatorWith_comp`;
  `standardOperatorWith_eq_smul` (`μ' = c μ` gives `c r_μ`).
- `exists_standardOperatorFun_apply_zero_ne_zero`, `standardOperatorWith_ne_zero`: at `x = 0` the
  indicator of a small compact open subgroup `L` goes to `μ{q | c̄ q ∈ L} > 0` (the phase
  `ψ(½ β(cy, ay))` is `1` there).

**The measure `d_g` and `r(g)`.** By `exists_pos_schwartzBruhatInner_map`
(`Langlands.Theta.Heisenberg.InvariantForm`), `⟨r_μ φ, r_μ φ'⟩_ν = C ⟨φ, φ'⟩_ν` with `C > 0` for
every Haar measure `ν` on `X` (`exists_pos_standardOperatorWith_inner`,
`schwartzBruhatInner_map_of_haar`, `schwartzBruhatInner_smul_measure`).

- `standardConstant g = C` for `μ = addHaar`, `standardScalar g = C^{-1/2}`,
  `standardMeasure g = C^{-1/2} addHaar`: **the measure `d_g`**.
- `standardOperator g = r(g)`, the operator of `d_g` (**Definition 2.9, Proposition 2.13**;
  `standardOperator_apply` is (2.16)); `standardOperator_eq_smul`.
- `standardOperator_inner`: `r(g)` is unitary for every Haar measure on `X`;
  `standardOperatorWith_inner_iff`: **`d_g` is the unique Haar measure on `Y ⧸ ker c` making the
  operator unitary**.
- `standardOperator_comp`: `r(g) ∘ σ(h) = σ(g · h) ∘ r(g)`.
- `standardOperator_injective` (unitarity), `standardOperator_surjective` (`r(g) r(g⁻¹)` commutes
  with `σ`, hence is a non-zero scalar by Schur's lemma `Renard.Smooth.sigmaCompactSchur`),
  `standardOperatorEquiv`.
- `standardPair g = (g, r(g))`: **the section `s_r` of p. 54** into
  `MetaplecticGroup (schrodingerModel hψ)`; `proj_standardPair`, `weil_standardPair`,
  `standardPair_mem_unitary` (`Mp(W)^{ℂ¹}`).

`schrodingerModel hψ` is `schrodingerSB` with the continuity of `β` read off the module topologies.

The book obtains the unitary normalization from Schur's lemma for unitary representations
(Proposition 1.21); here it comes from the uniqueness of invariant forms on the Schrödinger model,
and the measure is a definite Haar measure `d_g` on `Y ⧸ ker c`.

## Declarations

- Blocks: `isometryInv`, `standardC`, `standardC_apply`, `standardKernel`, `mem_standardKernel`,
  `polarizedForm_isometryInv`, `pairing_isometryInv_kernel`, `standardD`, `standardB`, `standardA`,
  `isometryInv_apply_eq`, `pairing_standardD_standardA`.
- Integrand: `standardIntegrand`, `standardIntegrand_add_kernel`, `standardIntegrand_schrodinger`,
  `standardIntegrand_eq`, `standardIntegrandQ`, `standardIntegrandQ_mk`, `continuous_isometryInv_mk`,
  `continuous_standardIntegrand`, `continuous_standardIntegrandQ`, `standardCQ`, `standardCQ_mk`,
  `standardCQ_injective`, `hasCompactSupport_standardIntegrandQ`.
- Operator: `standardOperatorFun`, `integrable_standardIntegrandQ`, `standardIntegrandQ_add`,
  `standardIntegrandQ_smul`, `standardOperatorFun_schrodinger`, `isPerfectBicharacter_pairing`,
  `standardOperatorFun_mem`, `schrodingerModel`, `standardOperatorWith`,
  `standardOperatorWith_apply`, `standardOperatorWith_comp`,
  `exists_standardOperatorFun_apply_zero_ne_zero`, `standardOperatorWith_ne_zero`.
- Normalization: `schwartzBruhatInner_smul_measure`, `schwartzBruhatInner_map_of_haar`,
  `standardOperatorWith_eq_smul`, `exists_pos_standardOperatorWith_inner`, `standardConstant`,
  `standardConstant_pos`, `standardOperatorWith_addHaar_inner`, `standardScalar`,
  `standardScalar_pos`, `standardScalar_sq_mul`, `standardMeasure` (with its `IsAddHaarMeasure`
  instance), `standardOperator`, `standardOperator_apply`, `standardOperator_eq_smul`,
  `standardOperator_inner`, `standardOperatorWith_inner_iff`, `standardOperator_comp`,
  `standardOperator_injective`, `standardOperator_surjective`, `standardOperatorEquiv`,
  `standardOperatorEquiv_apply`, `standardPair`, `proj_standardPair`, `weil_standardPair`,
  `standardPair_mem_unitary`.

All in the name space `Langlands.Theta`.

## Dependencies

`Langlands.Theta.Metaplectic.Defs`, `Langlands.Theta.Metaplectic.Exact`
(`continuous_isometryAction`), `Langlands.Theta.Heisenberg.InvariantForm`,
`Langlands.Theta.Heisenberg.SchrodingerInduced` (`continuous_pairing`),
`Langlands.HarmonicAnalysis.FiniteDimensionalQuotient`,
`Langlands.HarmonicAnalysis.Bicharacter.DualMeasure` (`isPerfectBicharacter_of_nondegenerate`).
