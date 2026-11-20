# Real and complex coordinates adapted to the imaginary axis

Module `Langlands.Global.ImaginaryAxisCoordinates` (namespace
`Langlands.Global.ImaginaryAxis`) builds coordinates on the parameter spaces
`X^*(P) ⊗ ℝ` and `X^*(P) ⊗ ℂ` in which the imaginary parameters
`i𝔞_P^*` form the slice `x ↦ i x` of `ℂⁿ`. It also computes the real part
and the root forms in these coordinates. It is a helper for the proof of
Lapid's Proposition 6 (Task 5613).

## Generic part

For an abelian group `X`, regarded as a `ℤ`-module:

- `complexify : ℝ ⊗ X →ₗ[ℝ] ℂ ⊗ X`, `r ⊗ χ ↦ r ⊗ χ`.
- `map_I_eq_smul_complexify`: the map `μ ↦ iμ`, that is
  `AlgebraTensorModule.map (toSpanSingleton ℝ ℂ i) id`, the published
  `imaginaryParameter`, equals `i • complexify`.
- `map_re_map_I`: the real part `AlgebraTensorModule.map reLm id`, the
  published `parameterRealPart`, vanishes on `iμ`.
- `finiteDimensional_real`: if `ℂ ⊗ X` is finite dimensional over `ℂ`,
  then `ℝ ⊗ X` is finite dimensional over `ℝ`. The proof uses
  `ℂ ⊗[ℝ] (ℝ ⊗ X) ≅ ℂ ⊗ X` (`cancelBaseChange`) and
  `rank_ℂ (ℂ ⊗[ℝ] V) = rank_ℝ V`.
- `realCoordinates : ℝⁿ ≃ ℝ ⊗ X` comes from Mathlib's `Module.finBasis`.
  `complexCoordinates : ℂⁿ ≃ ℂ ⊗ X` comes from the base-changed basis, whose
  vectors are the complexified basis vectors (`complexBasis_apply`).
- `complexCoordinates_ofReal`: `complexCoordinates (x : ℂⁿ) =
  complexify (realCoordinates x)` for real `x`.
- `imaginarySlice x = (i x_j)_j` and `complexCoordinates_imaginarySlice`:
  `complexCoordinates (imaginarySlice x) = iμ` with
  `μ = realCoordinates x`. So the imaginary parameters are exactly the image
  of the slice.

## Root forms

For a parabolic `P` with root presentation `r`:

- `rootFunctional_complexify`: `rootFunctional β (complexify y) =
  realRootFunctional β y`. The complex root form of the published
  `AdelicRootHyperplaneStatement` is real on complexified real parameters.
- `realRootFunctional_parameterRealPart_imaginaryParameter`: root forms
  vanish on the real part of an imaginary parameter.
- `not_isRegularParameter_of_le`: if `B(Re λ|_A, β) ≤ R` for a root `β` of
  `A` in the unipotent radical, then `λ` is not `R`-regular in the sense of
  the published `ParabolicRootPresentation.IsRegularParameter`.

## Provenance

Internal. Linear algebra of base change, used to put Lapid's parameter
spaces `𝔞_P^*` and `i𝔞_P^*` (Lapid 2011, §2, p.311) in coordinates.
