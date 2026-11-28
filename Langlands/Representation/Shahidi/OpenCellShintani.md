# Shintani uniqueness for the Jacquet function of the two-block section

Module `Langlands.Representation.Shahidi.OpenCellShintani`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `sum_liftFunction_fullΦ_mul_labelledRep`: for `ψ` of conductor `𝒪` and a system of
  representatives `σ : Λ → 𝒪` of the residue field (`|Λ| = q`, injective and surjective modulo
  the maximal ideal), the lift of `fullΦ` satisfies the minuscule Hecke relations of
  `χ = sectionParameter K a c s` at every point `g`:
  `∑_α F(g · labelledRep α) = q^(k(N-k)/2) e_k(χ) F(g)`.
- `liftFunction_fullΦ_mul_torus_neg_one`, `prod_sectionParameter`: for `ψ` of conductor `𝒪`, the
  central element `ϖ⁻¹` acts on the lift by `(∏ χ)⁻¹ = (∏ a_i ∏ c_j)⁻¹`.
- `sum_jacquetFunction_mul_labelledRep`: if a lift satisfies `∑_α F(h · labelledRep α) = E F(h)`
  for every `h`, and the Jacquet integrands at the points `g · labelledRep α` are integrable,
  then the Jacquet function satisfies the same relation at `g`;
  `jacquetFunction_mul_torus_neg_one`: a central relation `F(h ϖ⁻¹) = ω F(h)` for every `h`
  passes to the Jacquet function (no integrability needed).
- `integrable_jacquetIntegrandAt_of_torus`: for a Levi-invariant `Φ`, Levi-equivariant for the
  standard characters, integrability of the Jacquet integrand at every torus point implies it
  at every point.
- `jacquetFunction_fullΦ_eq_smul`: for `ψ` of conductor `𝒪`, if the Jacquet integrands of the
  section are integrable at every torus point, then `J = J(1) · W°(·; sectionParameter K a c s)`.

## Proof

The Jacquet function is left `(N, θ_ψ)`-equivariant, right `GL(𝒪)`-invariant, satisfies the
minuscule Hecke relations and the central relation; the Library's uniqueness theorem for
spherical Whittaker functions (`Conductor.eq_smul_sphericalWhittaker`) gives the conclusion.

## Provenance

Shintani's characterization of class-one Whittaker functions (Shintani 1976,
`shintani-1976-class-one-whittaker`, p. 180) as implemented in the Library.
