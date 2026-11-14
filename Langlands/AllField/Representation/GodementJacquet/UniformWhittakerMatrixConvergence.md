# All-field port of `Langlands.Representation.GodementJacquet.UniformWhittakerMatrixConvergence`

`Langlands.AllField.Representation.GodementJacquet.UniformWhittakerMatrixConvergence` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.UniformWhittakerMatrixConvergence`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.UniformWhittakerMatrixConvergence` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Common matrix convergence on actual coefficient models**

A uniform finite-function Mellin threshold and the fixed unipotent-slice
exponents give one matrix-convergence half-plane before all model functions
and full-matrix tests. Finite smooth-dual averaging transfers that bound to
the actual bi-smooth coefficient span. The uniform Mellin premise is explicit.

## Imports from the port

- `Langlands.AllField.LocalField.SmoothCharacterNormProofSupplement`
- `Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement`
- `Langlands.AllField.Representation.Geometric.GeometricLemmaStatement`
- `Langlands.AllField.Representation.GodementJacquet.UniformWhittakerSliceBound`
- `Langlands.AllField.Representation.GodementJacquet.WhittakerModelRationality`
- `Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatementSupplement`
- `Langlands.AllField.Representation.RankinSelberg.UniformFiniteFunctionMellinConvergenceStatement`
- `Langlands.AllField.Representation.Whittaker.TypeAsymptoticProof`

## Declarations

- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.uniform_torusMellin` (theorem): Tail-product change of variables preserves a single half-plane chosen
  before every pair of additive test functions.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.lintegral_torus_lt_top_of_uniform_terms` (theorem): The unipotent/torus estimate at a fixed parameter, using the common
  finite family and fixed slice exponents.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.exists_common_matrix_halfPlane` (theorem): One fixed finite torus family gives one convergence threshold for all
  Whittaker-like functions with expansions in that family and all matrix tests.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.exists_common_glModel_halfPlane` (theorem): A common shifted half-plane precedes every functional, model vector and
  matrix test, using a fixed coefficient-torus expansion.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.modelCoefficient_converges_of_modelFunctions` (theorem): Common convergence for model functions transfers to an individual actual
  smooth coefficient at the same parameter.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.exists_common_modelMatrix_halfPlane` (theorem): One common half-plane for every actual bi-smooth coefficient of every
  coefficient model, including reducible originals and the zero functional.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.exists_modelMatrixConvergenceBound` (theorem): Full Whittaker type supplies the fixed expansion through the published
  asymptotic proof. Only uniform Mellin convergence remains an explicit premise.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.modelMatrixConvergenceBound` (def): A common real convergence bound on all actual coefficient models of a
  full Whittaker-type representation. The uniform Mellin premise is explicit.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.modelMatrixConvergenceBound_spec` (theorem): The chosen bound precedes the functional, full-matrix test, actual
  bi-smooth coefficient and spectral parameter.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.glModel_matrixConvergesOnRight` (theorem): Common shifted matrix convergence on each actual coefficient-model
  representation, under uniform finite-function Mellin convergence.
