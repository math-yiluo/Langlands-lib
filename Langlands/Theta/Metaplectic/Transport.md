# The standard Weil operator under an isomorphism of polarized spaces

**GKT §2.3.1** (Definition 2.9, p. 54, and Proposition 2.13, p. 55: `r(g)` with the measure `d_g`
that makes it unitary), for the standard Weil operator of
`Langlands.Theta.Metaplectic.StandardOperator`.

The module `Langlands.Theta.Metaplectic.Transport` shows that `r(g)` does not depend on how the
polarized space is written: an isomorphism of polarized spaces carries the standard operators, with
their measures, and the scalars of the composition rule.

## Setting

Pairings `β : X →ₗ[F] Y →ₗ[F] F`, `β' : X' →ₗ[F] Y' →ₗ[F] F` and linear isomorphisms
`eX : X ≃ₗ[F] X'`, `eY : Y ≃ₗ[F] Y'` with `he : ∀ x y, β' (eX x) (eY y) = β x y`; then
`eX × eY` is an isometry of the polarized forms (`polarizedForm_prodCongr`).

## Content

Over a commutative ring:

- `isometryGroupCongr eX eY he : Sp(X × Y) ≃* Sp(X' × Y')`, `g ↦ (eX × eY) g (eX × eY)⁻¹`
  (`isometryGroupCongr_apply`, `isometryInv_isometryGroupCongr`).
- `standardKernel_isometryGroupCongr`: `eY (ker c(g)) = ker c(e g e⁻¹)`; `standardQuotientCongr`:
  the induced isomorphism `Y ⧸ ker c(g) ≃ Y' ⧸ ker c(e g e⁻¹)`.
- `standardIntegrand_isometryGroupCongr`, `standardIntegrandQ_standardQuotientCongr`: the integrand
  of `r(e g e⁻¹)` at `(eX x, eY y)` and `φ` is that of `r(g)` at `(x, y)` and `φ ∘ eX`.

Over a nonarchimedean local field (finite-dimensional spaces with the module topology, Borel
σ-algebras):

- `schwartzBruhatComp eX : S(X') ≃ₗ[ℂ] S(X)`, `φ ↦ φ ∘ eX` (`schwartzBruhatComp_apply`);
  the image of a Haar measure under a linear isomorphism is a Haar measure (the instance
  `isAddHaarMeasure_map_linearEquiv` of `Langlands.HarmonicAnalysis.FiniteDimensionalQuotient`);
  `schwartzBruhatInner_schwartzBruhatComp`:
  `⟨φ ∘ eX, φ' ∘ eX⟩_{eX⁻¹_* ν} = ⟨φ, φ'⟩_ν`.
- `standardOperator_isometryGroupCongr`: **`(r(e g e⁻¹) φ) ∘ eX = r(g) (φ ∘ eX)`**. Proof: the image
  of `d_g` under `standardQuotientCongr` is `s · d_{e g e⁻¹}` with `s > 0` (`exists_map_eq_smul`),
  so `T⁻¹ r(g) T = s · r(e g e⁻¹)` for `T = schwartzBruhatComp eX`; both sides are unitary for every
  Haar measure on `X'` (`standardOperator_inner` and the transport of the `L²` forms), so `s = 1`
  (`eq_of_eq_smul_of_inner`).
- `standardOperator_comp_isometryGroupCongr`: if `r(g₁) r(g₂) = z r(g₁ g₂)`, then
  `r(e g₁ e⁻¹) r(e g₂ e⁻¹) = z r(e g₁ g₂ e⁻¹)`.

## Declarations

`polarizedForm_prodCongr`, `isometryGroupCongr`, `isometryGroupCongr_apply`,
`isometryInv_isometryGroupCongr`, `standardKernel_isometryGroupCongr`,
`standardIntegrand_isometryGroupCongr`, `standardQuotientCongr`,
`standardIntegrandQ_standardQuotientCongr`, `schwartzBruhatComp`, `schwartzBruhatComp_apply`,
`schwartzBruhatInner_schwartzBruhatComp`,
`standardOperator_isometryGroupCongr`, `standardOperator_comp_isometryGroupCongr`. All in the name
space `Langlands.Theta`.

## Dependencies

`Langlands.Theta.Metaplectic.Block` (with `StandardOperator`, `SiegelParabolic`:
`standardOperator_inner`, `eq_of_eq_smul_of_inner`),
`Langlands.HarmonicAnalysis.FiniteDimensionalQuotient` (`exists_map_eq_smul`,
`linearEquivToContinuousAddEquiv`).

## Literature

W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025), §2.3.1,
Definition 2.9, p. 54, and Proposition 2.13, p. 55.
