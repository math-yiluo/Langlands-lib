# Residue-normalized additive Haar scaling over general local fields

Author: Worker 378.

This module states three internal prerequisites for the general-field Shahidi
intertwining operator, and their conjunction. It proves none of them. All four
declarations are transparent proposition definitions with the field `F` as an
explicit parameter, for

`F : Type uF` with `[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`.

This covers every nonarchimedean local field, including positive characteristic.
Unlike `PadicHaarScalingStatement`, nothing restricts `F` to a `PadicField`.

## Shared normalization premises

Each of the three statements begins with the same quantifiers, copied from
`Langlands.Shahidi.GeneralJacquetStabilizationStatement`:

- `q : ℕ` with `q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer)`,
  the cardinality of the residue field of the specified valuation ring;
- a real absolute value `abv : AbsoluteValue F ℝ`;
- `ϖ : Fˣ` with `Langlands.GeneralLinear.Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ`,
  so `v ϖ < 1` and every nonzero value is an integer power of `v ϖ`;
- `abv ϖ = (q : ℝ)⁻¹`;
- `abv x = 1` for every `x` with `ValuativeRel.valuation F x = 1`.

Every nonzero `x` is `ϖ^k u` with `v u = 1`, so these premises force
`abv x = q^(-k)`: `abv` is the residue-normalized absolute value. They fix the
normalization only. No scaling identity, regularity, or countability is assumed.

## The three statements

`Langlands.HarmonicAnalysis.GeneralScalarHaarScalingStatement F`: for every Borel
measurable structure on `F` (`[MeasurableSpace F] [BorelSpace F]`), every
additive Haar measure `μ` on `F`, and every field unit `a : Fˣ`,

`μ.map (fun x => (a : F) * x) = ((Shahidi.absUnits abv a : ℝ≥0)⁻¹) • μ`.

`Langlands.HarmonicAnalysis.GeneralRectangularHaarScalingStatement F`: for all
`r s : ℕ` (zero included), every Borel measurable structure on
`Matrix (Fin r) (Fin s) F` (entrywise product topology), every additive Haar
measure `μ` on it, and every `A : GeneralLinear r F`, `B : GeneralLinear s F`,

`μ.map (fun X => A * X * B⁻¹) = (((determinantAbs abv r A : ℝ≥0) ^ s / (determinantAbs abv s B : ℝ≥0) ^ r)⁻¹) • μ`.

`Langlands.HarmonicAnalysis.GeneralModulusScalingStatement F`: for all positive
`m, n`, every Borel measurable structure on `F` with `[MeasurableAdd₂ F]`, and
every additive Haar measure `μ` on `Matrix (Fin n) (Fin m) F` (product
measurable structure), `Langlands.Shahidi.IsModulusScaling hm hn abv μ`.

`Langlands.HarmonicAnalysis.GeneralAdditiveHaarScalingStatement F` is the
conjunction of the three.

The components are named separately so that their proofs can be developed and
reviewed separately; none of the three is a premise of another.

## Factors and coercions

All scalar factors are elements of `ℝ≥0`, the scalar type of `Measure.smul`
used by the published Haar and Shahidi APIs.

- `Langlands.Shahidi.absUnits abv : Fˣ →* ℝ≥0ˣ` sends a unit `a` to `abv a`. In
  (1) the factor is `((Shahidi.absUnits abv a : ℝ≥0)⁻¹)`: the unit is coerced to
  `ℝ≥0` and then inverted in `ℝ≥0`. The published lemma
  `Langlands.Shahidi.absUnits_apply` gives `((absUnits abv a : ℝ≥0) : ℝ) = abv a`
  by `rfl`.
- `Langlands.Shahidi.determinantAbs abv r : GeneralLinear r F →* ℝ≥0ˣ` is
  `absUnits abv` composed with the determinant, and
  `Langlands.Shahidi.determinantAbs_apply` gives
  `((determinantAbs abv r A : ℝ≥0) : ℝ) = abv (Matrix.det A.val)` by `rfl`. In
  (2) both determinant factors are coerced to `ℝ≥0` first. The powers, the
  quotient and the outer inverse are then taken in `ℝ≥0`.
- Matrices enter (2) through the coercion of `A : GeneralLinear r F` to
  `Matrix (Fin r) (Fin r) F`, and of the group inverse `B⁻¹ : GeneralLinear s F`
  to `Matrix (Fin s) (Fin s) F`. The map is the actual matrix product
  `X ↦ A * X * B⁻¹` on `Matrix (Fin r) (Fin s) F`.
- (3) uses the existing `Langlands.Shahidi.IsModulusScaling hm hn abv μ`
  unchanged. Its factor is `(leviModulus abv (twoBlocks n m hn hm) l : ℝ≥0)`.

These are the same factor shapes as `T.normalizedAbsUnits a` and
`T.determinantNorm` in `Langlands.HarmonicAnalysis.PadicHaarScalingStatement`,
with the residue-normalized `abv` replacing the p-adic realization.

## Pushforward inverse orientation

`μ.map f` is the pushforward: `(μ.map f) E = μ (f ⁻¹' E)`. For `f x = a * x`,
`f ⁻¹' E = a⁻¹ E`, so the expected scaling `μ (a E) = |a| μ E` gives
`(μ.map f) E = |a|⁻¹ μ E`. This is why (1) has the inverse factor. In the same way,
`X ↦ A X B⁻¹` is an `F`-linear automorphism of the `r s`-dimensional space
`Matrix (Fin r) (Fin s) F`. Left multiplication by `A` has determinant `det(A)^s`.
Right multiplication by `B⁻¹` has determinant `det(B)^(-r)`. The pushforward
therefore scales by the inverse of `|det A|^s / |det B|^r`.

## Swapped-block modulus orientation

`IsModulusScaling hm hn abv μ` is defined in
`Langlands/Representation/Shahidi/IntertwiningInduced.lean` for `μ` on
`Matrix (Fin n) (Fin m) F`, which is the `(n, m)` block order, not `(m, n)`. It
says that for every `l : (twoBlocks n m hn hm).Levi F`,

`μ.map (rectangularConj (l 0) (l 1)) = (leviModulus abv (twoBlocks n m hn hm) l : ℝ≥0) • μ`,

where `l 0 : GeneralLinear n F`, `l 1 : GeneralLinear m F`, and
`rectangularConj h₂ h₁ X = h₂⁻¹ * X * h₁`. The published lemma
`Langlands.Shahidi.leviModulus_twoBlocks` rewrites the factor as
`determinantAbs abv n (l 0) ^ m / determinantAbs abv m (l 1) ^ n`.

Take `r = n`, `s = m`, `A = (l 0)⁻¹` and `B = (l 1)⁻¹` in (2). Then `B⁻¹ = l 1`,
so the map in (2) is `rectangularConj (l 0) (l 1)`. The factor in (2) is the
inverse of `|det (l 0)|^(-m) / |det (l 1)|^(-n)`, which is
`|det (l 0)|^m / |det (l 1)|^n`, the factor above. So (3) is the special case of
(2) at the swapped `(n, m)` Levi, apart from the measurable-structure bookkeeping
below. It is stated separately because it is the form the general Shahidi
intertwining operator consumes, without an inverse factor.

## Measurable-structure premises

(1) quantifies over every `[MeasurableSpace F] [BorelSpace F]`. (2) quantifies
over every `[MeasurableSpace (Matrix (Fin r) (Fin s) F)]` with
`[BorelSpace (Matrix (Fin r) (Fin s) F)]` for the entrywise product topology,
exactly as in the p-adic rectangular statement. It needs no measurable structure
on `F`.

(3) must supply the instance arguments of `IsModulusScaling`, which are
`[MeasurableSpace F] [MeasurableAdd₂ F] [MeasurableMul F]`. The matrix space then
carries the product σ-algebra. The statement quantifies over
`[MeasurableSpace F] [BorelSpace F] [MeasurableAdd₂ F]`. Lean infers
`MeasurableMul F` as `ContinuousMul.measurableMul`; this was confirmed by
`#synth` in a private check. `MeasurableAdd₂ F` is an explicit premise because
the environment's Mathlib has no `SecondCountableTopology` instance derived from
`IsNonarchimedeanLocalField`, and so it cannot infer `MeasurableAdd₂ F` for a
Borel structure.

This premise is only a typing argument. It does not restrict which local fields
are covered. A nonarchimedean local field is second countable, so every Borel
structure on it satisfies `MeasurableAdd₂`, and the product σ-algebra on the
matrix space is its Borel σ-algebra. This module does not prove either fact.
A proof of (3) must derive the second fact (for example by `Pi.borelSpace`) to
apply (2) or the generic rectangular theorem. No regularity, σ-finiteness or
measure normalization is assumed anywhere.

## Rank-zero cases

(2) quantifies over all `r s : ℕ`, including `r = 0` or `s = 0`. Then
`Matrix (Fin r) (Fin s) F` is a singleton. `GeneralLinear 0 F` is trivial, and
its determinant is `1`. Every exponent that does not vanish has a base of
absolute value `1`, so the displayed factor is `1`. (3) is stated only for
`0 < m` and `0 < n`, because `IsModulusScaling` and `twoBlocks` take these
positivity proofs.

## Internal provenance

These are internal prerequisites, not transcriptions of a literature theorem.
Worker 99 extracted them from the generalization of the Shahidi intertwining
operator to arbitrary nonarchimedean local fields (task
`8e607558-e8b2-49f9-a778-9da15e3f4ac1`). They are the general-field counterparts of
`Langlands.HarmonicAnalysis.PadicScalarHaarScalingStatement` and
`Langlands.HarmonicAnalysis.PadicRectangularHaarScalingStatement`, together with
the conclusion of the published p-adic model
`Langlands.PadicField.TopologicalData.isModulusScaling_padic`. Mathematically:
(1) is the standard fact that the module of multiplication by `a` on a local
field is the normalized absolute value `q^(-v(a))`. (2) is the
finite-dimensional change of variables for the linear map `X ↦ A X B⁻¹`. (3) is
(2) at the `(n, m)` Levi. All three are proof obligations, not premises. This
module leaves the published p-adic statements unchanged.

## Helper lemmas for a later proof

The context of this task proposes the following route. It is not a proved
assertion of this module.

- Scalar law (1). Mathlib's `MeasureTheory.distribHaarChar` is the distributive
  Haar character, and `MeasureTheory.distribHaarChar_mul` (for `[Regular μ]`)
  gives `distribHaarChar A g * μ s = μ (g • s)`. `MeasureTheory.distribHaarChar_eq_div` and
  `MeasureTheory.distribHaarChar_eq_of_measure_smul_eq_mul` compute it on one set of finite
  positive measure. `MeasureTheory.Measure.isAddLeftInvariant_eq_smul` (which
  needs `SecondCountableTopology`) and
  `MeasureTheory.Measure.isAddLeftInvariant_eq_smul_of_regular` compare two Haar
  measures. `AddSubgroup.index_mul_measure` relates index and measure.
  `IsNonarchimedeanLocalField.isCompact_closedBall` and `Valuation.isOpen_integer`
  (in `Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean`) make the
  valuation ring compact and open. The residue index of the maximal ideal
  is `q`, and the uniformizer and unit premises then identify `distribHaarChar` with
  `abv`. The p-adic proof in `Langlands/HarmonicAnalysis/PadicScalarHaarScalingProof.lean`
  follows this route. Its key lemmas are private and specific to
  `PadicField.TopologicalData`, so they are a model, not something to import.
- Rectangular law (2). `Langlands/HarmonicAnalysis/PadicRectangularHaarScalingProof.lean`
  contains public field-generic theorems in namespace `Langlands.HarmonicAnalysis`:
  `productMeasure_preserving_transvection`, `productMeasure_map_diagonal`,
  `productMeasure_map_matrix`, `haarMeasure_map_matrix`,
  `haarMeasure_map_in_coordinates`, `rectangularCoordinates`,
  `rectangularCoordinates_mul`, and `haarMeasure_map_rectangular`. The last one
  needs `[Field K] [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
  [BorelSpace K] [SecondCountableTopology K] [LocallyCompactSpace K]`, a scalar
  Haar measure `ν`, a character `χ : K →*₀ ℝ≥0`, and the scalar law
  `∀ a ≠ 0, ν.map (a * ·) = (χ a)⁻¹ • ν`. It gives
  `μ.map (fun X => A * X * B) = (χ (det A) ^ card n * χ (det B) ^ card m)⁻¹ • μ`.
  Applied with `B` replaced by the matrix of `B⁻¹`, and with `χ` built from `abv`,
  it gives (2) once (1) and second countability of `F` are available.
- Modulus law (3). `Langlands.Shahidi.leviModulus_twoBlocks` together with
  `determinantAbs` and the orientation computation above reduce (3) to (2). The
  p-adic proof `isModulusScaling_padic` in
  `Langlands/Representation/Shahidi/IntertwiningPadic.lean` is the model.
