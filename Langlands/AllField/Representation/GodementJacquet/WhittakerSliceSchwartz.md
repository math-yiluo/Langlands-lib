# All-field port of `Langlands.Representation.GodementJacquet.WhittakerSliceSchwartz`

`Langlands.AllField.Representation.GodementJacquet.WhittakerSliceSchwartz` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.WhittakerSliceSchwartz`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.WhittakerSliceSchwartz` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Unipotent slices of matrix test functions are Schwartz–Bruhat**

For a p-adic field, a nontrivial additive character `ψ` and a compactly
supported locally constant function `f` on all square matrices, the function
`x ↦ ∫_N f(u · diag(x)) ψ(u) du` on `F^(n+1)` is Schwartz–Bruhat. See the
paired Markdown for the route.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.Zeta`

## Declarations

- `Langlands.AllField.GodementJacquet.WhittakerSlice.nabs` (abbrev): The canonical residue-normalized absolute value.
- `Langlands.AllField.GodementJacquet.WhittakerSlice.nabs_nonneg` (theorem).
- `Langlands.AllField.GodementJacquet.WhittakerSlice.nabs_mul` (theorem).
- `Langlands.AllField.GodementJacquet.WhittakerSlice.nabs_add_le_max` (theorem).
- `Langlands.AllField.GodementJacquet.WhittakerSlice.nabs_neg` (theorem).
- `Langlands.AllField.GodementJacquet.WhittakerSlice.nabs_zero` (theorem).
- `Langlands.AllField.GodementJacquet.WhittakerSlice.nabs_one` (theorem).
- `Langlands.AllField.GodementJacquet.WhittakerSlice.nabs_pos` (theorem).
- `Langlands.AllField.GodementJacquet.WhittakerSlice.continuous_nabs` (theorem).
- `Langlands.AllField.GodementJacquet.WhittakerSlice.eventually_small_scalar` (theorem): Small absolute value eventually lands in every neighbourhood of zero.
- `Langlands.AllField.GodementJacquet.WhittakerSlice.exists_small_matrix` (theorem): Entrywise small matrices lie in every neighbourhood of zero.
- `Langlands.AllField.GodementJacquet.WhittakerSlice.exists_uniform_constancy` (theorem): A compactly supported locally constant function on square matrices is
  invariant under all entrywise sufficiently small perturbations.
- `Langlands.AllField.GodementJacquet.WhittakerSlice.eq_of_small_diff` (theorem): Comparison of two values of such a function: it suffices that the entrywise
  difference is small whenever one of the two values is nonzero.
- `Langlands.AllField.GodementJacquet.WhittakerSlice.exists_support_bound` (theorem): The entries of the matrices in the support of a compactly supported function
  are uniformly bounded.
- `Langlands.AllField.GodementJacquet.WhittakerSlice.column_bound` (theorem): A column of a unipotent upper triangular matrix is bounded once the column
  scaled by `y` is bounded, provided `|y|` is bounded below away from the first
  column.
- `Langlands.AllField.GodementJacquet.WhittakerSlice.adjacentTransvection` (def): The elementary unipotent matrix `1 + c E_(i,i+1)`.
- `Langlands.AllField.GodementJacquet.WhittakerSlice.mul_adjacentTransvection_val` (theorem): Right multiplication by `1 + c E_(i,i+1)` adds `c` times column `i` to
  column `i+1`.
- `Langlands.AllField.GodementJacquet.WhittakerSlice.standardCharacter_adjacentTransvection` (theorem): The standard character takes the value `ψ(c)` on `1 + c E_(i,i+1)`.
- `Langlands.AllField.GodementJacquet.WhittakerSlice.sliceIntegral` (def): The unipotent slice integral `x ↦ ∫_N f(u · diag(x)) ψ(u) du` for the
  normalized Haar measure on the upper unipotent group.
- `Langlands.AllField.GodementJacquet.WhittakerSlice.sliceIntegral_eq_zero_of_invariant` (theorem): If the integrand's test-function factor is invariant under right translation
  by `1 + c E_(i,i+1)` with `ψ(c) ≠ 1`, the slice integral vanishes.
- `Langlands.AllField.GodementJacquet.WhittakerSlice.sliceIntegral_eq_zero_step` (theorem): One vanishing step: if `|x_i| ≥ t` (or `i = 0`) and `|x_(i+1)|` is below the
  threshold attached to `t`, the slice integral vanishes.
- `Langlands.AllField.GodementJacquet.WhittakerSlice.sliceIntegral_eq_zero_of_lt_threshold` (theorem): Vanishing by induction: for `b ≠ 0`, if `|x_b| < θ b` then the slice
  integral vanishes.
- `Langlands.AllField.GodementJacquet.WhittakerSlice.exists_character_ne_one` (theorem): A nontrivial additive character differs from one at some nonzero point.
- `Langlands.AllField.GodementJacquet.WhittakerSlice.sliceIntegral_isLocallyConstant` (theorem): The slice integral of a compactly supported locally constant function is
  locally constant.
- `Langlands.AllField.GodementJacquet.WhittakerSlice.sliceIntegral_hasCompactSupport` (theorem): The slice integral of a compactly supported function has compact support:
  it vanishes unless every `x_j` is a diagonal entry of a matrix in the support.
- `Langlands.AllField.GodementJacquet.WhittakerSlice.sliceIntegral_mem` (theorem): The slice integral of a Schwartz–Bruhat function on square matrices is
  Schwartz–Bruhat on `F^(n+1)`.
- `Langlands.AllField.GodementJacquet.WhittakerSlice.rightMulHomeomorph` (def): Right multiplication by an invertible matrix, as a homeomorphism of all
  square matrices.
- `Langlands.AllField.GodementJacquet.WhittakerSlice.sliceIntegral_rightTranslate_mem` (theorem): The slice integral of a right translate `M ↦ Φ(M k)` of a matrix test
  function is Schwartz–Bruhat on `F^(n+1)`.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.WhittakerSlice.exists_nhds_add_invariant`, `Langlands.GodementJacquet.WhittakerSlice.pi_eventually_small`, `Langlands.GodementJacquet.WhittakerSlice.threshold`, `Langlands.GodementJacquet.WhittakerSlice.threshold_pos`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
