# All-field port of `Langlands.Representation.GodementJacquet.WhittakerAveraging`

`Langlands.AllField.Representation.GodementJacquet.WhittakerAveraging` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.WhittakerAveraging`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.WhittakerAveraging` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Left compact averaging of Whittaker model functions**

JPS (1979), equations (3.1.3)–(3.1.4): averaging a Whittaker function on the
left over a compact open subgroup that fixes the test function gives a
bi-smooth matrix coefficient of the model with the same full-matrix integral.
Consequently `I₃ ⊆ I₂` for the actual coefficient model.

## Imports from the port

- `Langlands.AllField.Group.GL.CompactOpenSupplement`
- `Langlands.AllField.Group.GL.NormalizedCharacterSupplement`
- `Langlands.AllField.Representation.GodementJacquet.Zeta`

## Declarations

- `Langlands.AllField.GodementJacquet.Padic.exists_nhds_matrixTest_invariant` (theorem): A full-matrix test function is invariant under left multiplication by every
  element of some neighborhood of the identity.
- `Langlands.AllField.GodementJacquet.Padic.exists_compactOpen_matrixTest_invariant` (theorem): A compact open subgroup of `GL_(n+1)` fixing a full-matrix test function under
  left multiplication and lying in the kernel of the normalized determinant norm.
- `Langlands.AllField.GodementJacquet.Padic.modelSetIntegral` (def): The integral of model functions over a compact set, as a linear functional on
  the model.
- `Langlands.AllField.GodementJacquet.Padic.modelSetIntegralDual` (def): Integration over a compact open subgroup is a smooth functional on the model:
  it is fixed by that subgroup, by right invariance of the Haar measure.
- `Langlands.AllField.GodementJacquet.Padic.whittakerRationalValues_subset` (theorem): JPS (1979) (3.1.3)–(3.1.4): every rational value of a Whittaker integral on
  the actual model is a rational value of a bi-smooth matrix-coefficient integral of
  the model representation.
- `Langlands.AllField.GodementJacquet.Padic.jpssI3_le_jpssI2` (theorem): `I₃ ⊆ I₂` for the actual coefficient model of a smooth representation.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.setIntegral_mul_right_of_mem`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
