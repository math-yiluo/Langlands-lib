# All-field port of `Langlands.Representation.RankinSelberg.GammaFromWhittakerType`

`Langlands.AllField.Representation.RankinSelberg.GammaFromWhittakerType` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.GammaFromWhittakerType`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.GammaFromWhittakerType` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Gamma construction with dual Whittaker type derived from the original pair.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.PadicGammaFactor`

## Declarations

- `Langlands.AllField.RankinSelberg.PadicPairGammaConstructionInput` (def): Sufficient canonical p-adic inputs retaining original type, both analytic
  conclusions, self-duality and epsilon existence. Dual type is derived.
- `Langlands.AllField.RankinSelberg.padicPairGammaConstructionInput_iff` (theorem): The reduced inputs are equivalent to the published input predicate; the
  omitted dual type conditions follow from the original ones.
- `Langlands.AllField.RankinSelberg.padicPairGammaFactorOfWhittakerType` (def): The canonical p-adic gamma unit, with both dual Whittaker-type obligations
  discharged by transport.
- `Langlands.AllField.RankinSelberg.PadicSymmetricGammaConstructionInput` (def): Reduced construction inputs using the existing larger-rank-first convention.
- `Langlands.AllField.RankinSelberg.padicSymmetricGammaConstructionInput_iff` (theorem): The larger-rank-first input reduction works for both rank orders.
- `Langlands.AllField.RankinSelberg.padicSymmetricGammaFactorOfWhittakerType` (def): A certified gamma unit in either rank order with derived dual type.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.isOfWhittakerType_firstDual`, `Langlands.RankinSelberg.isOfWhittakerType_secondDual`, `Langlands.RankinSelberg.gammaFactorOfWhittakerType`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
