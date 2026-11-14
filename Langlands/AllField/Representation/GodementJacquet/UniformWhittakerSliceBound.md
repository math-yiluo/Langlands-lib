# All-field port of `Langlands.Representation.GodementJacquet.UniformWhittakerSliceBound`

`Langlands.AllField.Representation.GodementJacquet.UniformWhittakerSliceBound` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.UniformWhittakerSliceBound`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.UniformWhittakerSliceBound` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Uniform exponents for unipotent slices**

Choose the exponent using one fixed integral matrix box. Scalar dilation then
bounds every compact matrix support with this same exponent. The paired Markdown
records the construction and the resulting bound for Schwartz--Bruhat slices.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.WhittakerSliceBound`

## Declarations

- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.sliceExponents` (def): An exponent chosen from the unipotent-volume bound for the fixed integral
  matrix box. It depends on the field and rank, before every test or translate.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.unipotent_volume_bound_uniform` (theorem): The same exponents bound the volume for every compact matrix support.
  Only the cutoff unit and multiplicative constant depend on that support.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.exists_uniform_slice_bound` (theorem): Uniform slice bound: the exponents are fixed before both the full-matrix
  Schwartz--Bruhat test and its right translate.
