# Coefficient pairings between two representations with one central character

This module integrates products of matrix coefficients of two representations
over the central quotient `G ⧸ Subgroup.center G`. It is the analytic core of
the tempered discrete-series isotypic reduction: the integrals define a
four-linear form whose translation laws produce intertwiners in both
directions, and a positivity computation shows that a suitable value is nonzero.

Throughout, `ρ : Representation ℂ G V` and `σ : Representation ℂ G W` carry
prescribed unitary central characters `cρ`, `cσ`, and `hχ : cρ.character =
cσ.character`. All declarations live in namespace
`Langlands.UnitaryCentralCharacter`.

## The kernel on the central quotient

For `ℓ : Module.Dual ℂ W`, `w : W`, `η : Module.Dual ℂ V`, `v : V`, the function
`g ↦ ℓ(σ(g⁻¹)w) · η(ρ(g)v)` is invariant under right multiplication by central
elements (`pairingKernel_mul_center`): the central character factors
`χ(z)⁻¹` and `χ(z)` cancel because the two characters agree. Hence it descends
to `pairingKernel cσ hχ ℓ w η v : G ⧸ Subgroup.center G → ℂ`, with
`pairingKernel_mk` as its defining equation.

Elementary properties:

- `norm_pairingKernel`: its norm at `q` is
  `cσ.coefficientNorm ℓ w q⁻¹ * cρ.coefficientNorm η v q`;
- additivity and homogeneity in each of the four arguments
  (`pairingKernel_add_left`, `..._smul_left`, `..._add_vector_left`,
  `..._smul_vector_left`, and the four `_right` analogues);
- `pairingKernel_translate_right`: replacing `v` by `ρ(h)v` equals replacing the
  smooth functional `ℓ` by `smoothContragredient σ h⁻¹ ℓ` and translating the
  kernel on the right by the class of `h`;
- `pairingKernel_translate_left`: replacing `w` by `σ(h)w` and translating on
  the left by the class of `h` equals replacing the smooth functional `η` by
  `smoothContragredient ρ h⁻¹ η`;
- `continuous_pairingKernel`: for smooth `w` and `v` the kernel is continuous,
  since both coefficients are locally constant and the quotient map is a
  quotient map.

## Hölder integrability

`integrable_pairingKernel` assumes a Borel measure `μ` on the central quotient
that is invariant under inversion, smooth `w` and `v`, a real `r` with `1 < r`,
and

- `MemLp (cσ.coefficientNorm ℓ w) (ENNReal.ofReal r) μ`,
- `MemLp (cρ.coefficientNorm η v) (ENNReal.ofReal r.conjExponent) μ`.

It concludes `Integrable (pairingKernel cσ hχ ℓ w η v) μ`. Inversion invariance
transfers the first bound to `q ↦ cσ.coefficientNorm ℓ w q⁻¹`. The exponents
`r` and `r/(r-1)` are Hölder conjugate, so Mathlib's `MemLp.integrable_mul`
makes the product of the two norms integrable. The kernel is continuous, hence
almost-everywhere strongly measurable, and its norm equals that product.

## The integrated pairing

`coefficientPairing cσ hχ μ ℓ w η v` is the Bochner integral
`∫ q, pairingKernel cσ hχ ℓ w η v q ∂μ`, for smooth functionals
`ℓ : SmoothDual σ`, `η : SmoothDual ρ`. `PairingIntegrable cρ cσ hχ μ` is the
proposition that every such kernel with smooth functionals is integrable.
Integrability is not built into the definition; when it fails the Bochner
integral is zero by convention, and every lemma that needs it assumes
`PairingIntegrable`.

Under `PairingIntegrable`, `coefficientPairing` is additive in each argument
(`coefficientPairing_add_left`, `_add_vector_left`, `_add_right`,
`_add_vector_right`); homogeneity (`_smul_left`, `_smul_vector_left`,
`_smul_right`, `_smul_vector_right`) holds without it.

`coefficientPairing_translate_right` (for right-invariant `μ`) states
`coefficientPairing ℓ w η (ρ h v) =
coefficientPairing (smoothContragredient σ h⁻¹ ℓ) w η v`, by the kernel law and
`integral_mul_right_eq_self`. `coefficientPairing_translate_left` (for
left-invariant `μ`) states `coefficientPairing ℓ (σ h w) η v =
coefficientPairing ℓ w (smoothContragredient ρ h⁻¹ η) v`, by the kernel law and
`integral_mul_left_eq_self`.

## Intertwiners from the pairing

Both theorems assume `hcof` (every open subgroup contains a compact open
subgroup) and `PairingIntegrable cρ cσ hχ μ`.

- `exists_intertwiningMap_of_coefficientPairing_right`: if `ρ` is smooth, `σ`
  admissible and `μ` right invariant, then for each `w : W` and
  `η : SmoothDual ρ` there is `S : ρ.IntertwiningMap σ` with
  `smoothDualPairing σ ℓ (S v) = coefficientPairing ℓ w η v` for all `ℓ`, `v`.
- `exists_intertwiningMap_of_coefficientPairing_left`: if `σ` is smooth, `ρ`
  admissible and `μ` left invariant, then for each `ℓ : SmoothDual σ` and `v : V`
  there is `R : σ.IntertwiningMap ρ` with
  `smoothDualPairing ρ η (R w) = coefficientPairing ℓ w η v` for all `η`, `w`.

In each case the remaining two arguments form a bilinear map built with
`LinearMap.mk₂` from the linearity lemmas, the translation law is the hypothesis
of `exists_intertwiningMap_of_weakForm_of_compact_cofinal`
(`Smooth/Contragredient/WeakIntertwiner`), and that theorem supplies the
intertwiner.

## Positivity

`coefficientPairing_ne_zero` assumes `μ` positive on nonempty open sets, `σ`
smooth and irreducible, an invariant positive form `b : InvariantPositiveForm σ`,
a vector `u ≠ 0` whose coefficient `cσ.coefficientNorm (b.rightFunctional u) u`
is in `L²(μ)`, and `η : SmoothDual ρ`, `x : V` with
`η(ρ(g)x) = b.inner u (σ(g)u)` for all `g`. It concludes

`coefficientPairing (b.toSmoothDual hσ u) u η x ≠ 0`.

By invariance and conjugate symmetry of `b`, `b(u, σ(g⁻¹)u)` is the complex
conjugate of `b(u, σ(g)u)`, so the kernel is the real function
`q ↦ (cσ.coefficientNorm (b.rightFunctional u) u q)²`. The functional
`b.rightFunctional u` is nonzero because `b` is definite and `u ≠ 0`. If the
integral vanished, the Library theorem
`UnitaryCentralCharacter.eq_zero_of_integral_coefficientNorm_sq_eq_zero`
(`Unitary/SquareIntegrableProof`) would force `u = 0`.

## Provenance and scope

This module is an internal derived construction. Integrating products of
coefficients against a Levi representation is the mechanism of the
coefficient-algebra route of Silberger 1979, proofs of Theorems 3.3.1 and
4.5.18, as recorded in
[TemperedDiscreteSeriesIsotypicStatement](TemperedDiscreteSeriesIsotypicStatement.md).
The Lean route here differs: it uses no convolution algebra, Schur
orthogonality or formal degree, only weak integrals, the bidual isomorphism and
the positivity of `∫ |b(u, σ(g)u)|²`. Hölder's inequality
(`MemLp.integrable_mul`, `MeasureTheory/Function/L1Space/Integrable.lean`) and
integral translation invariance (`MeasureTheory/Group/Integral.lean`) come from
Mathlib at pinned commit `5ed2965256430c3649e86755f9576b54eca72435`.

No coefficient bound is proved here: the `L^r` bounds are hypotheses of
`integrable_pairingKernel`, and `PairingIntegrable` is a hypothesis of the
intertwiner theorems.
