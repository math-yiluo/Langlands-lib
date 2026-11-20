# Lebesgue-measure-preserving linear coordinate changes

Module `Langlands.Analysis.MeasurePreservingLinearCoordinates` collects
elementary facts about linear maps between coordinate spaces `ℝⁿ = Fin n → ℝ`
with Lebesgue measure `volume`. They are used to compare the induced inner
products `⟨φ, ψ⟩_P` built from two coordinate systems on `𝔞_P` that are related
by a Weyl-group isomorphism: the cut-off density `β` in one coordinate system
is transported to the other by a linear map of determinant `±1`.

## Provenance

Internal to the Library; standard facts about Haar measure on `ℝⁿ` (no
literature citation). They rely on Mathlib's scaling law
`MeasureTheory.Measure.addHaar_smul`, the nullity of proper subspaces
`MeasureTheory.Measure.addHaar_submodule`, and the image formula
`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar`.

## Declarations

- `eq_of_measurePreserving_linearMap`: a linear map `τ : ℝⁿ → ℝ^{n'}` that is
  measure preserving for Lebesgue measure forces `n = n'`. Proof: for the unit
  ball `B ⊆ ℝ^{n'}` one has `τ⁻¹(2 • B) = 2 • τ⁻¹(B)`. Measure preservation
  and the scaling law give `2^{n'} · vol(B) = 2^n · vol(B)`, and `vol(B)` is
  positive and finite, so `2^n = 2^{n'}` and `n = n'`.

- `surjective_of_measurePreserving_linearMap`: such a map is surjective. If
  its range were a proper subspace, the range would be Lebesgue-null, but its
  preimage is all of `ℝⁿ`, which has positive measure.

- `abs_det_eq_one_of_measurePreserving`: a measure-preserving linear map
  `τ : ℝⁿ → ℝⁿ` satisfies `|det τ| = 1`. It is surjective, hence bijective and
  `det τ ≠ 0`. Then the image of Lebesgue measure under `τ` is
  `|det τ|⁻¹ · volume`. Since this image is also `volume`, evaluating on the
  unit ball gives `|det τ|⁻¹ = 1`.

- `integral_comp_linearMap_of_abs_det_eq_one`: if `ρ : ℝⁿ → ℝⁿ` is linear with
  `|det ρ| = 1` and `f : ℝⁿ → ℝ` is a.e. strongly measurable, then
  `∫ f (ρ y) dy = ∫ f y dy`. The image of `volume` under `ρ` is
  `|det ρ|⁻¹ · volume = volume`, and the integral transforms by
  `MeasureTheory.integral_map`.

- `linearForm_comp_single_eq_transpose`: for a linear form `Φ` on `ℝⁿ` and a
  linear map `L : ℝⁿ → ℝⁿ`, the vector `j ↦ Φ (L eⱼ)` equals the transpose of
  the matrix of `L` applied to the vector `i ↦ Φ eᵢ`. Here `eᵢ` is the
  standard basis. The proof expands `L eⱼ = ∑ᵢ (L eⱼ)ᵢ eᵢ`.

- `det_toLin'_transpose_toMatrix'`: the linear map given by the transpose of
  the matrix of `L` has determinant `det L`.
