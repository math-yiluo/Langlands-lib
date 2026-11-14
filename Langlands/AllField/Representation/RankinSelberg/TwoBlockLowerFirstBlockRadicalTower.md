# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockRadicalTower`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockRadicalTower` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockRadicalTower`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockRadicalTower` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The radical tower for the actual lower mixed quotient**

The supplied rectangular Haar is unchanged. Its integral-cube mass is the
coefficient of the quotient measure composition in JPSS Section 4.9 (2).

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.EqualRankLastRowReductionProof`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockFiberProper`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockNormalization`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lintegral_mixedHaar_radical` (theorem): Right radical coordinates give the same product Haar as the published left coordinates.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lintegral_radicalFiberPoint_quotientAverageReal` (theorem): The lower radical integrates the mixed orbital average to the cube multiple
  of the normalized lower mixed average, at every representative.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lintegral_radicalKernel_comp_quotientAverageReal` (theorem): The composite radical kernel integrates mixed averages to cube multiples of
  lower mixed averages for every outer measure.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalKernel_comp` (theorem): Compatible quotient measures satisfy the full radical tower with the exact
  supplied rectangular cube coefficient.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalKernel_comp_restrict` (theorem): The radical has determinant one, so the full tower restricts to every
  matching determinant slice, including the zero outer slice in equation (2).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.RadicalTowerStatement` (abbrev): The full radical tower and all matching determinant-slice restrictions.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalTower` (theorem): Compatible measures satisfy the exact full and restricted radical tower.
