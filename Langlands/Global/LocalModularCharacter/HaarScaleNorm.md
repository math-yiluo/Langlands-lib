# Haar scaling of linear automorphisms over number-field completions

Author: Worker 1402.

This helper module proves the Haar normalization lemma used in the proof of
`Langlands.Global.PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement`.
Let `F` be a number field, `i : Place F` a place, `K = placeCompletion F i` the actual
completion, and `A` a `K`-linear automorphism of `Fin d → K`. Then the additive Haar
character of `A` is the normalized absolute value of its determinant:

`addEquivAddHaarChar (placeLinearContinuousAddEquiv F i A) = placeNorm F i (det A)`,

that is, `A` multiplies additive Haar measure of `K^d` by `‖det A‖ ^ m` at an infinite
place of multiplicity `m` (one at a real place, two at a complex one), and by `‖det A‖` at a
finite place, for the existing norm of the adic completion.

## Provenance

This is the classical fact that the modulus of a linear automorphism of `K^d` over a local
field `K` is the modulus of its determinant: Weil, *Basic Number Theory*, second edition
(source `weil-1973-basic-number-theory`), Chapter I, §2, Corollary 3 of Theorem 3, p. 7,
states `mod_V(A) = mod_K(det A)`, where `mod` is the factor by which a map multiplies Haar
measure of images. Mathlib's `addEquivAddHaarChar φ` is that factor (it satisfies
`addEquivAddHaarChar φ • μ.map φ = μ`). It is derived content: the module states and proves it for the
normalizations already in the Library, namely Mathlib's `addEquivAddHaarChar` and the
Library's `placeNorm` (`Langlands.Global.AdelicLocalCharacterNorm`). It adds no definition
beyond the two wrappers below and the auxiliary character `unitsCharWithZero`.

## Declarations

All declarations are in namespace `Langlands.Global`.

- `linearPiContinuousAddEquiv A`: for a topological commutative ring `K`, a finite type `ι`
  and `A : (ι → K) ≃ₗ[K] (ι → K)`, the continuous additive automorphism with underlying
  additive equivalence `A.toAddEquiv`. Continuity of `A` and `A.symm` is Mathlib's
  `LinearMap.continuous_on_pi`. The simp lemma `coe_linearPiContinuousAddEquiv` states that
  its underlying function is `A`.
- `unitsCharWithZero χ`: a monoid homomorphism `χ : Kˣ →* ℝ≥0` on the units of a field,
  extended by zero to a `K →*₀ ℝ≥0`. `unitsCharWithZero_units` states that it agrees with
  `χ` on units.
- `addEquivAddHaarChar_linearPi_eq`: let `K` be a commutative ring that is a field
  (`IsField K`), with a second-countable locally compact ring topology and Borel measurable
  structure, and let `ι → K` carry any Borel measurable structure. If `ν` is an additive
  Haar measure on `K`, `χ : Kˣ →* ℝ≥0`, and `ν.map (a * ·) = (χ a)⁻¹ • ν` for every unit
  `a`, then `addEquivAddHaarChar (linearPiContinuousAddEquiv A) = χ (det A)`.
- `map_mul_left_eq_smul_of_ringEquiv`: if `e : K ≃+* k` and its inverse are continuous,
  `ν₀` is an additive Haar measure on `k` with `ν₀.map (e a * ·) = c • ν₀`, then
  `ν.map (a * ·) = c • ν` for every additive Haar measure `ν` on `K` (with `K` locally
  compact and second countable).
- `infiniteCompletion_map_mul_left w ν ha`: for an infinite place `w` of any field `F`, any
  Borel measurable structure on `w.Completion`, any additive Haar measure `ν` and `a ≠ 0`,
  `ν.map (a * ·) = (‖a‖₊ ^ w.mult)⁻¹ • ν`.
- `finiteCompletion_map_mul_left v ν a`: for a finite place `v` of a number field, any Borel
  measurable structure on `FiniteCompletion F v`, any additive Haar measure `ν` and any unit
  `a`, `ν.map (a * ·) = ‖a‖₊⁻¹ • ν`.
- `placeCompletion.isField F i`: every `placeCompletion F i` is a field.
- `placeCompletion_map_mul_left F i ν a`: the two previous scaling lemmas in the form
  `ν.map (a * ·) = (placeNormValue F i a)⁻¹ • ν` for every place and every unit `a`.
- `placeLinearContinuousAddEquiv F i A`: an abbreviation for `linearPiContinuousAddEquiv A`
  on `Fin d → placeCompletion F i`.
- `addEquivAddHaarChar_placeLinear_eq_placeNorm F i A`: the main statement displayed above,
  for any Borel measurable structure on `Fin d → placeCompletion F i`. The universe of `F`
  is arbitrary.

## Implemented proof

**Linear scaling.** In `addEquivAddHaarChar_linearPi_eq`, the given Borel measurable
structure on `ι → K` equals the product structure `MeasurableSpace.pi` (both are Borel, by
`Pi.borelSpace`), so the proof substitutes it. With `M` the matrix of `A`, the function of
`linearPiContinuousAddEquiv A` is `Matrix.toLin' M` and `det M = det A ≠ 0`. The Library
theorem `Langlands.HarmonicAnalysis.haarMeasure_map_matrix`, applied to the scalar scaling
hypothesis with the character `unitsCharWithZero χ`, gives
`addHaar.map (toLin' M) = (χ (det A))⁻¹ • addHaar`. Multiplying by `χ (det A)` (nonzero,
since `χ` takes units to units) gives `χ (det A) • addHaar.map A = addHaar`, and the
Library theorem `Langlands.HarmonicAnalysis.addEquivAddHaarChar_eq_of_smul_map` concludes.

**Transfer.** In `map_mul_left_eq_smul_of_ringEquiv`, `ν₀.map e.symm` is an additive Haar
measure on `K`, so Mathlib's uniqueness `isAddLeftInvariant_eq_smul` writes `ν` as a scalar
multiple of it. Since `(a * ·) ∘ e.symm = e.symm ∘ (e a * ·)`, pushing forward commutes with
the scalar, and the hypothesis on `ν₀` gives the claim.

**Infinite places.** At a real place, transfer along `ringEquivRealOfIsReal` to Lebesgue
measure on `ℝ`, where `Real.map_volume_mul_left` gives the factor `|b|⁻¹` for
`b = extensionEmbeddingOfIsReal a`; this embedding is an isometry and `w.mult = 1`. At a
complex place, transfer along `ringEquivComplexOfIsComplex` to `addHaar` on `ℂ`. Left
multiplication by `b` is the `ℝ`-linear map `Algebra.lmul ℝ ℂ b`, whose determinant is
`Algebra.norm ℝ b = ‖b‖ ^ 2`, so `Measure.map_linearMap_addHaar_eq_smul_addHaar` gives the
factor `(‖b‖ ^ 2)⁻¹`; again the embedding is an isometry and `w.mult = 2`.

**Finite places.** The proof applies the Library theorem
`Langlands.HarmonicAnalysis.generalScalarHaarScalingStatement` to the nonarchimedean local
field `FiniteCompletion F v` (`FiniteCompletion.valuativeRel` and
`FiniteCompletion.isNonarchimedeanLocalField`), with `q = Ideal.absNorm v.asIdeal` and the
absolute value of the existing norm. Its premises are checked as follows.

- The valuation `ValuativeRel.valuation` is equivalent to the adic valuation `Valued.v`
  (`ValuativeRel.isEquiv`, using that `Valued.v` is compatible).
- A uniformizer: `v.valuation_exists_uniformizer` gives `π ∈ F` with adic valuation
  `exp (-1)`. Its image `ϖ` in the completion has valuation less than one, and every nonzero
  `x` satisfies `v x = v (ϖ ^ (-log (Valued.v x)))`, so `ϖ` is a uniformizing element.
- The valuation subrings of the two equivalent valuations coincide, giving a ring
  isomorphism to `v.adicCompletionIntegers F`; with the Library's
  `CompletionResidue.card_adicResidueField` the residue field has `absNorm v.asIdeal`
  elements.
- `‖ϖ‖ = (absNorm v.asIdeal)⁻¹` by `NumberField.FinitePlace.norm_def` and the value
  `exp (-1)`, and `‖x‖ = 1` whenever the valuation of `x` is one.

**Place level.** `placeCompletion_map_mul_left` splits the place into its infinite and finite
cases and applies the two scalar lemmas (the values of `placeNormValue` agree with
`‖a‖₊ ^ w.mult` and `‖a‖₊` by definition). The main theorem equips `placeCompletion F i` with
its Borel structure and applies `addEquivAddHaarChar_linearPi_eq` with `ν = addHaar`,
`χ = placeNormValue F i` and this scaling lemma; the coercion of `placeNorm F i (det A)` is
`placeNormValue F i (det A)` by definition.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
