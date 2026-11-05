# Coefficients of `p_χ`-images (Waldspurger, proof of Theorem VIII.4.2, formula (2))

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralCoefficientFormula`,
namespace `Langlands.HarishChandraSchwartz`. It imports `KernelQuotient` and uses from it
`integral_centralProjection_mul_conj` (the pairing of `p_χ φ` with a `χ`-covariant function on
`A \ G`, through the Weil formula). Through that import it uses `CentralProjection`
(`centralProjection`, `centralProjection_mul_left`, `IsUnitaryCharacter`), `Convolution`
(`convolution`, `convolution_apply`), the published `Langlands.Group.LeftQuotient`
(`LeftQuotient`) and `Langlands.Analysis.Local.QuotientMeasure` (`IsCompatible`), both read in
namespace `Langlands.QuotientIntegration`. From Mathlib it uses
`MeasureTheory.integral_integral_swap`, `MeasureTheory.Integrable.integral_prod_left`,
`MeasureTheory.Integrable.bdd_mul`, `MeasureTheory.integral_mul_left_eq_self`,
`MeasureTheory.integral_inv_eq_self` and `MeasureTheory.integral_indicator_const`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234. Bars checked on the page image of printed p. 331 (text extraction drops them).

Proof of Theorem VIII.4.2 (`p_χ(°C(G)) = A₂(G)_χ`), inclusion `p_χ(°C(G)) ⊂ A₂(G)_χ`. Printed
p. 330 (PDF p. 96): `H` is a compact open subgroup, `°C(H \ G)` the elements of `°C(G)` left
invariant under `H`, `V = p_χ(°C(H \ G))`, and `ρ` the action of `G` on `V` by right
translations. Printed p. 331 (PDF p. 97): "Soient donc `f₁, f₂ ∈ V`, `g ∈ G`, introduisons
`φ₁, φ₂ ∈ °C(H \ G)` tels que `f₁ = p_χ φ₁`, `f₂ = p_χ φ₂`. On a les égalités:

`(f₁, ρ(g) f₂) = ∫_{A_G\G} conj(f₁(g′)) f₂(g′g) dg′`
`= ∫_{A_G\G} ∫_{A_G} conj(f₁(g′)) φ₂(g′ag) χ⁻¹(a) da dg′`
`= ∫_G conj(f₁(g′)) φ₂(g′g) dg′`
`= ∫_G ∫_{A_G} conj(φ₁(ag′)) χ(a) φ₂(g′g) da dg′`
`= ∫_{A_G} ∫_G χ⁻¹(a) conj(φ₁(g′)) φ₂(g′ag) dg da`
`= ∫_{A_G} χ⁻¹(a) (ˇφ̄₁ ∗ φ₂)(ag) da.`

La permutation des intégrales est justifiée car, si l'on remplace `φ₁` et `φ₂` par leurs
valeurs absolues, la dernière intégrale est absolument convergente. D'où l'égalité

`(f₁, ρ(g) f₂)_{A_G\G} = (p_χ(ˇφ̄₁ ∗ φ₂))(g).` (2)"

Then: "Soit maintenant `f ∈ V`. Appliquons l'égalité (2) à `f₂ = f` et `f₁ = p_χ °e`, où `e`
est la fonction caractéristique de `H`. On choisit `φ₁ = °e`. D'après la Remarque VIII.2.2,
`conj(ˇ°e) = °e`. D'après le Lemme VIII.2.3, puisque `φ₂ ∈ °C(H \ G)`,
`°e ∗ φ₂ = e ∗ φ₂ = mes(H) φ₂`. D'où l'égalité `f(g) = mes(H)⁻¹ (p_χ °e, ρ(g) f)_{A_G\G}`."

On the page image the left side of `conj(ˇ°e) = °e` carries both a bar and a check, as does
`ˇφ̄₁` in (2); bar and check commute, and `ˇφ̄₁(h) = conj(φ₁(h⁻¹))`. So Remark VIII.2.2 is used
in the single form `conj(°e(x⁻¹)) = °e(x)`, which is exactly what replaces `ˇφ̄₁` by `°e`.
Waldspurger's `p_χ` is `(p_χ f)(g) = ∫_{A_G} χ⁻¹(a) f(ag) da` (VIII.4, printed p. 327, PDF
p. 93), which is `centralProjection`, and his convolution is
`(f₁ ∗ f₂)(g) = ∫_G f₁(h) f₂(h⁻¹g) dh` (III.6, printed p. 271, PDF p. 37), which is
`convolution`.

## Scope: abstract data and explicit hypotheses

The module proves the computation of (2) and of the reproducing identity for abstract
functions; it does not construct `°C(H \ G)`, `°e` or `V`, does not prove Remark VIII.2.2 or
Lemma VIII.2.3, and does not prove the absolute convergence quoted above or the square
integrability of (2) on `A_G \ G` ("En particulier cette fonction est de carré intégrable").
Waldspurger's `(f₁, ρ(g) f₂)_{A_G\G}` is written as the integral
`∫_{A\G} conj(f₁(q̇)) f₂(q̇ g) dν(q)` with `q̇ = Quotient.out q`.

**Section `Correlation`.** `G` is a group with a measurable structure, `μG` a measure on `G`,
`φ₁, φ₂, φ, E : G → ℂ`, and `H` a subgroup.

- `coefficientCorrelation_eq_convolution`: `[MeasurableInv G]`, `[μG.IsInvInvariant]`.
- `coefficientCorrelation_eq_convolution_self`: `[MeasurableInv G]`, `[μG.IsInvInvariant]`,
  `hEc : ∀ x, conj (E x⁻¹) = E x` (Waldspurger's `conj(ˇ°e) = °e`, Remark VIII.2.2).
- `indicator_convolution_eq`: `hH : MeasurableSet (H : Set G)` and left invariance
  `hφ : ∀ h ∈ H, ∀ x, φ (h * x) = φ x`. No invariance of `μG` is needed.
- `convolution_eq_of_convolution_eq_indicator_left`: `hH`, a measure `μH` on `H` with
  `hμH : μH.map Subtype.val = μG.restrict H` (`μH` is the restriction of `μG`, so
  `μH(H) = mes(H)`), `hφ`, and
  `hE : ∀ x, convolution μG E φ x = convolution μG ((H : Set G).indicator fun _ => 1) φ x`
  (Waldspurger's `°e ∗ φ₂ = e ∗ φ₂`, Lemma VIII.2.3).

**Section `OnG`.** Moreover `[MeasurableMul G]`; `A` is a subgroup with a measurable structure
and `[MeasurableInv A]`; `μA` is an s-finite, inversion-invariant measure on `A`; `μG` is
s-finite and left invariant; `χ : A →* ℂˣ`. Each result uses only the instances it needs (the
others are omitted in the Lean source).

- `integrable_coefficientIntegrand`: `hχ : IsUnitaryCharacter χ` (`|χ| = 1` and `χ`
  measurable) and the absolute convergence
  `hint : Integrable (fun p : G × A => conj (φ₁ ((p.2 : G) * p.1)) * φ₂ (p.1 * g))
  (μG.prod μA)`.
- `conj_centralProjection_mul_eq`: `hχ` only.
- `integrable_conj_centralProjection_mul`: `[SFinite μA]`, `hχ`, `hint`.
- `integral_conj_centralProjection_mul`: all section instances, `hAc : A ≤ Subgroup.center G`,
  `hχ`, `hint`.
- `centralProjection_const_mul`: none.

**Section `Quotient`.** The setting of the Weil formula of `KernelQuotient`: `G` is a
Hausdorff, locally compact, second countable topological group with its Borel structure; `μG`
is finite on compacts, s-finite and left invariant; `A` is a closed subgroup
(`hA : IsClosed (A : Set G)`) with its Borel structure, `[MeasurableInv A]`, and `μA` is
s-finite, right invariant, inversion invariant and finite on compacts; `LeftQuotient A` (the
cosets `A g`, Waldspurger's `A_G \ G` for `A = A_G`) carries its Borel structure and a measure
`ν`.

- `integral_conj_centralProjection_mul_centralProjection`: `hA`, `[MeasurableMul A]`,
  `hν : IsCompatible A μG μA ν` (`ν` nonzero, regular, right invariant, and the Weil formula
  for compactly supported continuous functions), `hAc`, `hχ`, `hint`.
- `integral_conj_centralProjection_mul_centralProjection_eq_mul`: `hA`, `[MeasurableMul A]`,
  `[MeasurableInv G]`, `[μG.IsInvInvariant]`, `hν`, `hAc`, `hχ`, `hEc`,
  `hconv : ∀ x, convolution μG E φ x = c * φ x`, and `hint` for `φ₁ = E`, `φ₂ = φ`.
- `centralProjection_eq_inv_mul_integral`: `hA`, `[MeasurableMul A]`, `[MeasurableInv G]`,
  `[μG.IsInvInvariant]`, `hν`, `hAc`, `hχ`, a subgroup `H` with `hH`, `μH` with `hμH`,
  `hmes : (μH Set.univ).toReal ≠ 0`, `hEc`, `hφ`, `hE`, and `hint` for `φ₁ = E`, `φ₂ = φ`.

In Waldspurger's situation `A = A_G` is central and closed, `μG` and `μA` are Haar measures
(`G` is unimodular), `ν` is the quotient measure, `χ ∈ Â_G` is unitary, `E = °e`,
`φ, φ₂ ∈ °C(H \ G)`, and `hint` is the absolute convergence he states for the double integral.

## Definitions

- `coefficientCorrelation μG φ₁ φ₂ x = ∫_G conj(φ₁(g′)) φ₂(g′x) dμG(g′)`: Waldspurger's
  `ˇφ̄₁ ∗ φ₂` written without the substitution `h = g′⁻¹`; it equals `ˇφ̄₁ ∗ φ₂` when `μG` is
  inversion invariant (`coefficientCorrelation_eq_convolution`). It is the inner integral
  `∫_G conj(φ₁(g′)) φ₂(g′ag) dg′` in the fifth line of the display, at `x = ag`.
- `coefficientIntegrand χ φ₁ φ₂ g (g′, a) = χ(a) conj(φ₁(ag′)) φ₂(g′g)`: the integrand of the
  fourth line of the display, as a function on `G × A`.

## Results

- `coefficientCorrelation_eq_convolution`: `coefficientCorrelation μG φ₁ φ₂ x =
  convolution μG (fun h => conj (φ₁ h⁻¹)) φ₂ x`, i.e. `(ˇφ̄₁ ∗ φ₂)(x)`.
- `coefficientCorrelation_eq_convolution_self`: under `hEc`,
  `coefficientCorrelation μG E φ x = (E ∗ φ)(x)`.
- `indicator_convolution_eq` (**`e ∗ φ = mes(H) φ`**): for `e` the characteristic function of
  `H` and `φ` left invariant under `H`, `(e ∗ φ)(x) = μG(H) φ(x)`.
- `convolution_eq_of_convolution_eq_indicator_left` (**`°e ∗ φ₂ = e ∗ φ₂ = mes(H) φ₂`**):
  under `hE`, `(E ∗ φ)(x) = μH(H) φ(x)`.
- `integrable_coefficientIntegrand`: the integrand of the fourth line is integrable on
  `G × A`.
- `conj_centralProjection_mul_eq`: `conj((p_χ φ₁)(g′)) φ₂(g′g) = ∫_A χ(a) conj(φ₁(ag′)) φ₂(g′g)
  dμA(a)` (third line to fourth line).
- `integrable_conj_centralProjection_mul`: `g′ ↦ conj((p_χ φ₁)(g′)) φ₂(g′g)` is
  `μG`-integrable.
- `integral_conj_centralProjection_mul` (**formula (2) on `G`**):
  `∫_G conj((p_χ φ₁)(g′)) φ₂(g′g) dμG(g′) = (p_χ(coefficientCorrelation μG φ₁ φ₂))(g)` (third
  line equals the last).
- `centralProjection_const_mul`: `p_χ(c φ) = c p_χ φ`.
- `integral_conj_centralProjection_mul_centralProjection` (**formula (2)**):
  `∫_{A\G} conj((p_χ φ₁)(q̇)) (p_χ φ₂)(q̇ g) dν(q) = (p_χ(coefficientCorrelation μG φ₁ φ₂))(g)`,
  i.e. `(f₁, ρ(g) f₂)_{A\G} = (p_χ(ˇφ̄₁ ∗ φ₂))(g)` when `μG` is inversion invariant.
- `integral_conj_centralProjection_mul_centralProjection_eq_mul`: under `hEc` and `hconv`,
  `(p_χ E, ρ(g) p_χ φ)_{A\G} = c (p_χ φ)(g)`.
- `centralProjection_eq_inv_mul_integral` (**reproducing identity**): under `hEc`, `hφ`, `hE`,
  `hμH` and `hmes`, `(p_χ φ)(g) = mes(H)⁻¹ (p_χ E, ρ(g) p_χ φ)_{A\G}` with
  `mes(H) = μH(H)`, i.e. Waldspurger's `f(g) = mes(H)⁻¹ (p_χ °e, ρ(g) f)_{A_G\G}`.

## Proof notes

1. `coefficientCorrelation_eq_convolution`: `integral_inv_eq_self` (substitution
   `h ↦ h⁻¹`); the `_self` version rewrites `conj(E(h⁻¹))` to `E(h)` by `hEc`.
2. `indicator_convolution_eq`: for `h ∈ H`, `φ(h⁻¹x) = φ(x)` by `hφ`, so the integrand of
   `(e ∗ φ)(x)` is the indicator of `H` times the constant `φ(x)`
   (`integral_indicator_const`). The `_left` version identifies `μH(H)` with `μG(H)` through
   `hμH` (`Measure.map_apply`).
3. `conj_centralProjection_mul_eq`: `conj(χ(a)⁻¹) = χ(a)` since `|χ(a)| = 1`; then
   `integral_conj` and `integral_mul_const`.
4. `integrable_coefficientIntegrand`: `Integrable.bdd_mul` with the bound `|χ| ≤ 1`;
   `integrable_conj_centralProjection_mul` is its partial integral over `A`
   (`Integrable.integral_prod_left`) rewritten by step 3.
5. `integral_conj_centralProjection_mul`: step 3 rewrites the left side as the iterated
   integral `∫_G ∫_A`; `integral_integral_swap` (Fubini, using `hint`) exchanges the
   integrals; for fixed `a`, left invariance of `μG` (`integral_mul_left_eq_self`, substitution
   `g′ ↦ a g′`) and centrality of `a⁻¹` give
   `∫_G χ(a) conj(φ₁(ag′)) φ₂(g′g) dg′ = χ(a) coefficientCorrelation(a⁻¹g)`; inversion
   invariance of `μA` (`integral_inv_eq_self`, `a ↦ a⁻¹`) turns
   `∫_A χ(a) coefficientCorrelation(a⁻¹g) da` into `p_χ(coefficientCorrelation)(g)`.
   Waldspurger performs both substitutions at once in his fifth line.
6. `integral_conj_centralProjection_mul_centralProjection`: `integral_centralProjection_mul_conj`
   of `KernelQuotient`, applied to the `χ`-covariant `K = p_χ φ₁`
   (`centralProjection_mul_left`) and `φ = φ₂(· g)`, with the integrability of step 4, turns
   the quotient integral into the integral over `G` of step 5 (first to third line of the
   display); here `(p_χ φ₂)(q̇ g) = (p_χ(φ₂(· g)))(q̇)` by definition.
7. `integral_conj_centralProjection_mul_centralProjection_eq_mul`: step 6 with `φ₁ = E`,
   step 1 (`_self`) and `hconv` inside `p_χ`, then `centralProjection_const_mul`.
8. `centralProjection_eq_inv_mul_integral`: step 7 with `c = μH(H)` given by step 2 (`_left`),
   multiplied by `μH(H)⁻¹` (`hmes`).

## Relation to the Library

- `KernelDiagonal` proves the right-sided analogues used in Proposition VIII.4.1,
  `convolution_indicator_eq` (`φ ∗ e = mes(H) φ` for right `H`-invariant `φ`) and
  `convolution_eq_of_convolution_eq_indicator`; the left-sided versions here are those used in
  Theorem VIII.4.2. They are proved directly (no left invariance of `μG` is needed on this
  side).
- `KernelReproduction` and `KernelQuotient` treat formula (1) of Proposition VIII.4.1, where
  the kernel `α_χ(·, g)` is fixed; formula (2) here concerns two arbitrary `p_χ`-images.
- `CentralProjection` has `Space.centralProjection`, the linear map `p_χ` on the Schwartz space
  `C(G)`; `centralProjection_const_mul` is the pointwise scalar rule for arbitrary functions,
  which is what is needed here because `φ` is not assumed to lie in `C(G)`.
- The reproducing identity is the input `f(g) = (e, ρ(g) f)` (with `e = mes(H)⁻¹ p_χ °e`)
  of the abstract inclusion `V ⊂ A₂(G)_χ`; the square integrability of (2) on `A_G \ G`, the
  other input of that inclusion, is not proved here.

## Open obligations

The construction of `°e` and `°C(H \ G)` (VIII.2, which depends on Theorem VII.2.5), Remark
VIII.2.2 (`conj(ˇ°e) = °e`, i.e. `hEc`), Lemma VIII.2.3 (`hE`), the absolute convergence
`hint` for `φ₁, φ₂ ∈ °C(H \ G)`, and the square integrability of the right side of (2) on
`A_G \ G` are not proved here.
