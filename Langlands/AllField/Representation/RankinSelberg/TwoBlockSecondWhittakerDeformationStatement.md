# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationStatement`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Entire standard-character deformation on the second lower-induced block**

A derived transport of the published first-block inverse-character deformation
from JPSS 1983, Section (4.5), printed pages 408-409. Only the second block is
multiplied by `|det|^u`; the family is the actual canonical normalized lower
parabolic induction on the original ordered dependent block carriers.

The closed proposition is stated here, without its proof. Its paired Markdown
explains character change, the parameter `-u`, and the global determinant twist
needed to transport the published theorem. No representation comparison or
analytic family is assumed in the proposition.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockWhittakerDeformationStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.twoBlockSecondDeformedBlocks` (abbrev): The original ordered blocks with only the second block twisted by `|det|^u`.
  The field and every dependent block carrier keep their original universes.
- `Langlands.AllField.RankinSelberg.twoBlockSecondDeformedInduced` (abbrev): The deformed representation `ρ_u`: canonical normalized lower parabolic
  induction of the deformed blocks to `GL_(t+1)`.
- `Langlands.AllField.RankinSelberg.twoBlockSecondDeformedBlocks_zero` (theorem): At `u = 0` the deformed blocks are the original blocks.
- `Langlands.AllField.RankinSelberg.TwoBlockSecondWhittakerDeformationStatement` (def): Derived second-block standard-character form of the published first-block
  inverse-character deformation. Every coefficient of every nonzero standard
  Whittaker functional at zero extends to actual coefficients at every complex
  parameter, with one compact open right level and pointwise entire dependence.
  This definition states the assertion; its transport proof is separate.
