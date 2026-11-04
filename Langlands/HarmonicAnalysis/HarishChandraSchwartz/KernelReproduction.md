# The kernel `α_χ` and its reproducing identity on `G` (Waldspurger VIII.4.1)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.KernelReproduction`,
namespace `Langlands.HarishChandraSchwartz`. It imports the published module
`CentralProjection` (for `centralProjection`, `IsUnitaryCharacter`,
`IsUnitaryCharacter.norm_inv`, `IsUnitaryCharacter.measurable_inv`), which imports
`Convolution` (for `convolution` and `convolution_apply`). From Mathlib it uses
`integral_inv_eq_self`, `integral_conj`, `Integrable.prod_right_ae`, `integral_prod`,
`integral_integral_swap`, `integral_prod_mul`, `Integrable.bdd_mul` and
`Complex.inv_eq_conj`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

Proof of Proposition VIII.4.1, printed pp. 328–329 (PDF pp. 94–95; bars checked on the page
images):

- p. 328: `e` is the characteristic function of `H` and `°e` its image under `°`; `°e` is
  real valued (by Remark VIII.2.2). For `g₁, g₂ ∈ G`,
  `α(g₁, g₂) = mes(H)⁻² ∫_H °e(g₁⁻¹ h g₂) dh` and
  `α_χ(g₁, g₂) = ∫_{A_G} α(g₁ a, g₂) χ⁻¹(a) da = ∫_{A_G} α(g₁, a g₂) χ(a) da`;
  `α_χ(·, g₂) = p_χ α(·, g₂)`.
- p. 328, formula (1) and its proof: for `f = p_χ φ` with `φ ∈ °C_H`,
  `(α_χ(·, g), f)_{A_G\G} = ∫_G conj(α_χ(g', g)) φ(g') dg'
  = mes(H)⁻² ∫_G ∫_{A_G} ∫_H °e(g'⁻¹ h a g) χ⁻¹(a) φ(g') dh da dg'`, an absolutely
  convergent expression, which equals
  `mes(H)⁻² ∫_{A_G} ∫_H φ * °e(h a g) χ⁻¹(a) dh da`.
- p. 329: since `φ ∈ °C_H`, Lemma VIII.2.3 gives `φ * °e = φ * e = mes(H) φ`; the integral
  over `H` disappears by left invariance of `φ`, and
  `(α_χ(·, g), f)_{A_G\G} = ∫_{A_G} φ(a g) χ⁻¹(a) da = f(g)`.

This module formalizes the definitions of `α` and `α_χ`, the equality of the two expressions
of `α_χ`, and the computation of `∫_G conj(α_χ(g', g)) φ(g') dg'`. The first equality of (1),
which identifies the quotient product `(α_χ(·, g), f)_{A_G\G}` with this integral over `G`, is
not formalized here.

## Scope: abstract data and explicit hypotheses

- `G` is a group with a measurable structure and a measure `μ` (`[SFinite μ]`); `μ` enters
  only through the convolution `convolution μ φ E (x) = ∫ φ(h) E(h⁻¹ x) dμ(h)`.
- `H` is any subgroup of `G` with a measure `μH` on `H` (`[SFinite μH]`); `mes(H)` is
  `(μH Set.univ).toReal`. In the application `μH` is the restriction of the Haar measure of
  `G` to the compact open subgroup `H`; this identification is not made here.
- `A` is a subgroup of `G` with a measurable structure (`[MeasurableInv A]`) and a measure
  `μA` (`[SFinite μA]`, `[μA.IsInvInvariant]`), for Waldspurger's `A_G` with its Haar measure.
- `χ : A →* ℂˣ` is a character, `E : G → ℂ` a function (for `°e`).

The hypotheses of each result:

- `conj_kernelAlpha`: `hE : ∀ x, conj (E x) = E x` (`E` is real valued).
- `kernelAlpha_mul_left`: `hA : A ≤ Subgroup.center G`.
- `kernelAlphaChi_eq`: `[MeasurableInv A]`, `[μA.IsInvInvariant]` and `hA`.
- `conj_kernelAlphaChi`: those of `kernelAlphaChi_eq`, `hχ : IsUnitaryCharacter χ` and `hE`.
- `integral_conj_kernelAlphaChi_mul`: `[SFinite μ]`, `[SFinite μA]`, `[SFinite μH]`,
  `[MeasurableInv A]`, `[μA.IsInvInvariant]`, `hA`, `hχ`, `hE`, and for `φ : G → ℂ`:
  - `hH : ∀ h ∈ H, ∀ x, φ (h * x) = φ x` (left invariance under `H`);
  - `hconv : ∀ x, convolution μ φ E x = (μH Set.univ).toReal * φ x` (Waldspurger's
    `φ * °e = mes(H) φ`, which he derives from Lemma VIII.2.3 and the right invariance of
    `φ`; here it is a hypothesis);
  - `hmes : (μH Set.univ).toReal ≠ 0`;
  - `hint`: the function `(g', a, h) ↦ E(g'⁻¹ h (a g)) φ(g')` is integrable for
    `μ.prod (μA.prod μH)` (Waldspurger's absolute convergence of the triple integral).

## Definitions

- `kernelAlpha μH E g₁ g₂ = mes(H)⁻² ∫_H E(g₁⁻¹ h g₂) dμH(h)`, Waldspurger's `α`.
- `kernelAlphaChi μA χ μH E g₁ g₂ = centralProjection μA χ (fun g => kernelAlpha μH E g g₂) g₁
  = ∫_A χ(a)⁻¹ α(a g₁, g₂) dμA(a)`, Waldspurger's `α_χ` (`α(a g₁, g₂) = α(g₁ a, g₂)` for central
  `A`). By definition `α_χ(·, g₂) = p_χ α(·, g₂)`.

## Results

- `conj_kernelAlpha`: `conj α(g₁, g₂) = α(g₁, g₂)` for real `E`.
- `kernelAlpha_mul_left`: `α(a g₁, g₂) = α(g₁, a⁻¹ g₂)` for `a ∈ A` central.
- `kernelAlphaChi_eq` (Waldspurger's second expression):
  `α_χ(g₁, g₂) = ∫_A χ(a) α(g₁, a g₂) dμA(a)`.
- `conj_kernelAlphaChi`: `conj α_χ(g₁, g₂) = ∫_A χ(a)⁻¹ α(g₁, a g₂) dμA(a)`.
- `integral_conj_kernelAlphaChi_mul` (**formula (1), integral over `G`**):
  `∫_G conj(α_χ(g', g)) φ(g') dμ(g') = (p_χ φ)(g) = centralProjection μA χ φ g`.

## Proof notes

- `kernelAlphaChi_eq`: by `kernelAlpha_mul_left`, `χ(a)⁻¹ α(a g₁, g₂) = χ(a⁻¹) α(g₁, a⁻¹ g₂)`;
  substitute `a ↦ a⁻¹` (`integral_inv_eq_self`).
- `conj_kernelAlphaChi`: conjugate under the integral (`integral_conj`); `α` is real and
  `conj χ(a) = χ(a)⁻¹` for `|χ(a)| = 1` (`Complex.inv_eq_conj`).
- Formula (1): by `conj_kernelAlphaChi`, `conj(α_χ(g', g)) φ(g')` is the iterated integral
  over `A` and `H` of `F(g', a, h) = χ(a)⁻¹ mes(H)⁻² E(g'⁻¹ h a g) φ(g')`. `F` is integrable on
  `G × A × H` by `hint`, since `|χ(a)⁻¹| = 1` (`Integrable.bdd_mul`). Fubini
  (`Integrable.prod_right_ae`, `integral_prod`, `integral_integral_swap`) moves the integral
  over `G` inside. There `∫_G E(g'⁻¹ h a g) φ(g') dμ(g') = (φ * E)(h a g) = mes(H) φ(h a g)
  = mes(H) φ(a g)` by `hconv` and `hH`. The remaining integrand depends only on `a`, so the
  integral over `A × H` is `mes(H) · ∫_A χ(a)⁻¹ mes(H)⁻¹ φ(a g) dμA(a)` (`integral_prod_mul`),
  which is `(p_χ φ)(g)` since `mes(H) ≠ 0`.

## Relation to the Library

- `centralProjection` (published, `CentralProjection`) is Waldspurger's `p_χ`;
  `kernelAlphaChi` is defined through it, so `α_χ(·, g₂) = p_χ α(·, g₂)` holds by definition.
- The companion module `SectionReproducingKernel` (submitted separately and not imported
  here) states the finiteness argument of VIII.4.1 for a reproducing kernel read through a
  section of `G → A_G\G`; the present identity is the computation on `G` behind its
  hypothesis `reproduce` for `K(y) = α_χ(·, y)`.
- No other Library declaration defines `α`, `α_χ` or proves this identity.

## Open obligations

The first equality of (1) (unfolding the quotient product over `A_G\G` through the Weil
formula and the `χ`-covariance of `α_χ(·, g)` and `f`), the definitions of `°e` and `°C_H`,
Lemma VIII.2.3 and the right `H`-invariance argument behind `hconv`, the absolute convergence
`hint`, and the identification of `μH` with the restriction of the Haar measure of `G` are not
proved here.
