# The standard Weil operator on the Siegel parabolic subgroup

**GKT §2.3.2** (the Siegel parabolic `P(X)`, `m(a)`, `n(b)`, `M(X)`, `N(X)`, p. 57;
**Lemma 2.16**, p. 58; **Proposition 2.17**, p. 59; **Corollary 2.18**, p. 60), for the standard
Weil operator `r(g)` of `Langlands.Theta.Metaplectic.StandardOperator`.

The module `Langlands.Theta.Metaplectic.SiegelParabolic` defines the Siegel parabolic of the
Lagrangian of the Schrödinger model, computes `r(p)` on it with the measure `d_p`, proves the
composition rule `r(p₁ g p₂) = r(p₁) r(g) r(p₂)` with the measures carried along, and obtains the
splitting of `P(X)`.

## Content

For a pairing `β : X →ₗ[R] Y →ₗ[R] R` the Lagrangian of the Schrödinger model of `polarizedForm β`
is `0 × Y` (the book's `X`); the functions live on `X` (the book's `Y`).

**The group** (any commutative ring).

- `siegelParabolicGroup β`: the isometries `p` with `p (0 × Y) = 0 × Y` (both inclusions,
  `mem_siegelParabolicGroup`). For them the c-part of `p⁻¹` vanishes (`standardC_eq_zero_of_mem`),
  `ker c = Y` (`standardKernel_eq_top_of_mem`), and the blocks `d`, `a` of `p⁻¹` are automorphisms
  (`siegelD`, `siegelA`; the book's `a^*` and `a⁻¹` in `p⁻¹ = [[a⁻¹, −b a^*], [0, a^*]]`) with
  `β(d x, a y) = β(x, y)` (`pairing_standardD_standardA_of_mem`, the book's (2.19)).
- `siegelLeviGroup.toIsometry_mem`: the Siegel Levi `siegelLeviGroup β` of
  `Langlands.Theta.Metaplectic.SiegelLevi` lies in it.
- `siegelUnipotentElement β b hb`: the book's `n(b)`, `(x, y) ↦ (x, y + b x)` for `b : X → Y` with
  `β(x, b x') = β(x', b x)` (the symmetry (2.20)); `siegelUnipotentElement_mem`.

**Lemma 2.16** (a nonarchimedean local field, `β` perfect, `ψ` continuous and non-trivial).

- `standardIntegrand_of_mem`, `standardOperatorWith_apply_of_mem`: on `P(X)` the integrand does not
  depend on `y`, and `r_μ(p) φ(x) = μ(Y ⧸ Y) ψ(½ β(d x, b x)) φ(d x)`.
- `standardMeasure_real_univ_of_mem`: `d_p(Y ⧸ Y) = |det d|^{1/2}` — the book's
  `∫_{ker(c(p⁻¹)) \ X} d_p x = |det a|^{1/2}`, obtained as in the book from unitarity, with
  `integral_comp_linearEquiv` (`∫ f(d x) dν = |det d|⁻¹ ∫ f dν`, from `map_linearEquiv_addHaar`).
- `standardOperator_of_mem_siegelParabolicGroup`: **`r(p) φ(x) = |det d|^{1/2} ψ(½ β(d x, b x))
  φ(d x)`** where `p⁻¹ (x, 0) = (d x, b x)`; in the book's coordinates
  `r(m(a) n(b)) φ(y) = ψ(½⟨a^* y, −b a^* y⟩) |det a|^{1/2} φ(a^* y)`.
- `standardOperator_siegelLevi`: on the Levi, `r(m)` is `siegelLeviWeil β m` (module `SiegelLevi`)
  (`φ ↦ |det a|^{-1/2} φ(a⁻¹ ·)`); `standardOperator_siegelUnipotentElement`:
  **`r(n(b)) φ(x) = ψ(−½ β(x, b x)) φ(x)`**, the book's `ψ(½⟨y, −b y⟩) φ(y)` — the unipotent part of
  Lemma 2.16.

**Proposition 2.17 with the measures.** The book argues that `r(gp)` and `r(g) r(p)` differ by a
scalar of modulus one, and evaluates both at `0` on a test function to show the scalar is
positive. Here the positivity comes from the integrals themselves:

- `exists_integral_quotientEquiv`: a linear isomorphism `e : Y ⧸ K ≃ Y ⧸ K'` carries a Haar measure
  to a positive multiple of a given one, so `∫ G(e q + t) dμ = s ∫ G dμ'` with `s > 0`.
- `standardKernel_mul_of_mem_right`: `ker c(g p) = ker c(g)`; `map_standardKernel_mul_of_mem_left`:
  `a` maps `ker c(p g)` onto `ker c(g)`.
- `exists_standardOperator_mul_of_mem_right`, `exists_standardOperator_mul_of_mem_left`: the
  integrands are related by `p⁻¹` (right) and by the affine substitution `y ↦ a y + b x` (left),
  so `r(g) r(p) = t r(g p)` and `r(p g) = t r(p) r(g)` with `t > 0`.
- `eq_of_eq_smul_of_inner`: two operators, each a positive multiple of the other and both unitary,
  are equal; `exists_schwartzBruhatInner_ne_zero` supplies the test function.
- `standardOperator_mul_of_mem_right`, `standardOperator_mul_of_mem_left`,
  `standardOperator_mul_mul_of_mem`: **`r(p₁ g p₂) = r(p₁) r(g) r(p₂)`**.

**Corollary 2.18.** `standardOperator_one` (`r(1) = 1`), `siegelParabolicWeil` (the
representation `p ↦ r(p)` of `P(X)`), `siegelParabolicWeil_normalizes`,
`siegelParabolicSplitting` (the splitting `p ↦ (p, r(p))`), `weil_siegelParabolicSplitting`,
`siegelParabolicSplitting_apply` (it is the standard section `standardPair`).

Corollary 2.21 (invariance of the Leray cocycle) needs the cocycle of Definition 2.7, which is not
defined here.

## Declarations

- `siegelParabolicGroup`, `mem_siegelParabolicGroup`, `standardC_eq_zero_of_mem`,
  `standardKernel_eq_top_of_mem`, `isometryInv_inv`, `siegelD`, `siegelD_apply`, `siegelA`,
  `siegelA_apply`, `pairing_standardD_standardA_of_mem`, `siegelLeviGroup.toIsometry_mem`,
  `siegelUnipotentElement`, `siegelUnipotentElement_apply`, `isometryInv_siegelUnipotentElement`,
  `siegelUnipotentElement_mem`.
- `standardIntegrand_of_mem`, `standardOperatorWith_apply_of_mem`, `integral_comp_linearEquiv`,
  `exists_schwartzBruhatInner_ne_zero`, `eq_of_eq_smul_of_inner`,
  `standardMeasure_real_univ_of_mem`, `standardOperator_of_mem_siegelParabolicGroup`,
  `exists_integral_quotientEquiv`, `isometryInv_mul`, `standardKernel_mul_of_mem_right`,
  `map_standardKernel_mul_of_mem_left`, `standardMeasure_real_univ_pos`,
  `exists_standardOperator_mul_of_mem_right`, `standardOperator_mul_of_mem_right`,
  `exists_standardOperator_mul_of_mem_left`, `standardOperator_mul_of_mem_left`,
  `standardOperator_mul_mul_of_mem`.
- `standardOperator_one`, `siegelParabolicWeil`, `siegelParabolicWeil_apply`,
  `siegelParabolicWeil_normalizes`, `siegelParabolicSplitting`, `weil_siegelParabolicSplitting`,
  `siegelParabolicSplitting_apply`, `standardOperator_siegelLevi`,
  `standardOperator_siegelUnipotentElement`.

All in the name space `Langlands.Theta`.

## Dependencies

`Langlands.Theta.Metaplectic.StandardOperator`, `Langlands.Theta.Metaplectic.SiegelLevi`
(`siegelLeviGroup`, `siegelLeviWeil`), through them
`Langlands.HarmonicAnalysis.FiniteDimensionalQuotient` and
`Langlands.HarmonicAnalysis.LinearHaarScaling` (`map_linearEquiv_addHaar`).
