# All-field port of `Langlands.Representation.GodementJacquet.WhittakerModelInclusion`

`Langlands.AllField.Representation.GodementJacquet.WhittakerModelInclusion` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.WhittakerModelInclusion`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.WhittakerModelInclusion` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Matrix-coefficient integrals of the model as sums of Whittaker integrals**

JPSS (1983), Section (5.2), printed 421: on an admissible coefficient model, every
smooth functional agrees with a finite combination of compact averages of
evaluations, and a conjugation change of variables turns each resulting integral
into a full-matrix Whittaker integral. Given convergence and rationality of every
Whittaker integral on the model, this gives `I₂ ⊆ I₃`.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.AnalyticData`
- `Langlands.AllField.Representation.GodementJacquet.ModelWhittakerRationalityStatement`
- `Langlands.AllField.Representation.GodementJacquet.WhittakerAveraging`
- `Langlands.AllField.Representation.GodementJacquet.WhittakerModelComparisonStatement`
- `Langlands.AllField.Representation.Unramified.SphericalConstituentExistenceProof`

## Declarations

- `Langlands.AllField.GodementJacquet.Padic.conjTest` (def): The conjugated test function `M ↦ Φ(h⁻¹ M h)`, again Schwartz–Bruhat on all
  square matrices.
- `Langlands.AllField.GodementJacquet.Padic.conjTest_apply` (theorem).
- `Langlands.AllField.GodementJacquet.Padic.matrixIntegrand_conj` (theorem): The pointwise identity behind the conjugation change of variables.
- `Langlands.AllField.GodementJacquet.Padic.measurePreserving_conj` (theorem): Conjugation by a fixed element preserves the normalized Haar measure.
- `Langlands.AllField.GodementJacquet.Padic.measurableEmbedding_conj` (theorem): Conjugation by a fixed element is a measurable embedding.
- `Langlands.AllField.GodementJacquet.Padic.integrable_conj_iff` (theorem): Conjugation change of variables, integrability: `Φ(g) |det g|^s u(hg)` is
  integrable exactly when the matrix integrand of the conjugated test against the
  right translate `y ↦ u(yh)` is.
- `Langlands.AllField.GodementJacquet.Padic.integral_conj` (theorem): Conjugation change of variables, value.
- `Langlands.AllField.GodementJacquet.Padic.glModelFunction_injective` (theorem): A vector of the coefficient model is determined by its model function.
- `Langlands.AllField.GodementJacquet.Padic.modelPointAverage` (def): The functional `W ↦ ∫_L W(hk) dk` on the model, for a compact open subgroup `L`.
- `Langlands.AllField.GodementJacquet.Padic.modelPointAverage_apply` (theorem): Unfolding the point average.
- `Langlands.AllField.GodementJacquet.Padic.modelPointAverage_invariant` (theorem): The point average is invariant under right translation by `L`.
- `Langlands.AllField.GodementJacquet.Padic.modelPointAverage_of_mem_fixedVectors` (theorem): On vectors fixed by `L`, the point average is `vol(L)` times evaluation at `h`.
- `Langlands.AllField.GodementJacquet.Padic.measureReal_openSubgroup_ne_zero` (theorem): A compact open subgroup has nonzero finite Haar mass.
- `Langlands.AllField.GodementJacquet.Padic.eq_zero_of_modelPointAverage_eq_zero` (theorem): A vector fixed by `L` on which every point average vanishes is zero.
- `Langlands.AllField.GodementJacquet.Padic.exists_eq_sum_modelPointAverage` (theorem): On an admissible coefficient model, every smooth functional agrees with a finite
  combination of point averages over some compact open subgroup inside a prescribed
  open subgroup.
- `Langlands.AllField.GodementJacquet.Padic.modelPointAverage_matrixIntegral` (theorem): JPSS (1983), printed 421: integrating the point average of the right translates
  of a model vector against `Φ(g)|det g|^s`, for `L` fixing `Φ` on the left and inside
  the kernel of `|det|`, gives `vol(L)` times the Whittaker integral of the conjugated
  test function at the right translate by `h`.
- `Langlands.AllField.GodementJacquet.Padic.glModel_isAdmissible` (theorem): The admissibility of `σ` passes to its coefficient model.
- `Langlands.AllField.GodementJacquet.Padic.ModelRationality` (def): The local form of `ModelWhittakerRationalityStatement`: every shifted Whittaker
  integral on the model converges on a right half-plane and is rational.
- `Langlands.AllField.GodementJacquet.Padic.exists_whittakerRationalValue` (theorem): A Whittaker integral of the model has a rational value lying in `I₃`, with an
  explicit half-plane of convergence.
- `Langlands.AllField.GodementJacquet.Padic.matrixIntegral_sum_modelPointAverage` (theorem): The matrix integral of a finite combination of point averages of right
  translates is the corresponding combination of Whittaker integrals of conjugated
  test functions, wherever all of the latter converge.
- `Langlands.AllField.GodementJacquet.Padic.exists_mem_jpssI3_of_coefficient` (theorem): JPSS (1983), printed 421: on an admissible model with rational Whittaker
  integrals, the integral of a matrix coefficient `g ↦ Λ(ρ(g)w)` of the model, for a
  smooth functional `Λ`, is a finite combination of Whittaker integrals, hence has a
  rational value in `I₃`.
- `Langlands.AllField.GodementJacquet.Padic.matrixRationalValues_subset_jpssI3` (theorem): Every rational value of a bi-smooth matrix-coefficient integral of the model lies
  in `I₃`, given admissibility of the model and rationality of its Whittaker integrals.
- `Langlands.AllField.GodementJacquet.Padic.jpssI2_le_jpssI3_of_rationality` (theorem): `I₂ ⊆ I₃` for the actual coefficient model, given admissibility of the model and
  rationality of its Whittaker integrals.
- `Langlands.AllField.GodementJacquet.whittakerModelComparison_of_rationality` (theorem): JPSS (1983), Section (5.2): `I₂ = I₃` on the actual coefficient model, assuming
  convergence and rationality of every Whittaker integral on that model.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.apply_averageMap_of_invariant`, `Langlands.GodementJacquet.eq_of_invariant_of_eqOn_fixedVectors`, `Langlands.GodementJacquet.exists_finsupp_eqOn_of_ker`, `Langlands.GodementJacquet.apply_of_mem_fixedVectors_dual`, `Langlands.GodementJacquet.exists_eq_sum_of_invariant`, `Langlands.GodementJacquet.biSmoothCoefficient_apply`, `Langlands.GodementJacquet.const_mul_mem_zetaSpan`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
