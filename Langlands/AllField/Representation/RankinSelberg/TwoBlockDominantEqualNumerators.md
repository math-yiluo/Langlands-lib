# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantEqualNumerators`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualNumerators` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantEqualNumerators`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantEqualNumerators` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Actual finite numerators at the equal-rank boundary**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualSecondBlock`

## Declarations

- `Langlands.AllField.RankinSelberg.DominantRankTransport.equalResidueCardinalityUnit` (def): The nonzero canonical residue cardinality, as a complex unit.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.coe_equalResidueCardinalityUnit` (theorem).
- `Langlands.AllField.RankinSelberg.DominantRankTransport.EqualFirstBlockFactorCertificate` (def): The complete first-block factor witnesses, retained before all tests.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.EqualTwoBlockFiniteNumerators` (def): Both first-block certificates and their actual finite numerator identities.
  The reversed first block has original polynomial `P₂D` and dual polynomial `P₂`.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.equalTwoBlockFiniteNumerators_of_laws` (theorem): The actual two-sided laws give finite numerators, with their full factor
  certificates common to every section, coefficient and Fourier pair.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.exists_equalTwoBlockFiniteNumerators` (theorem): Above one real bound, a nonzero ordinary Jacquet functional supplies both
  complete block certificates and finite numerators uniformly in the compatible
  quotient measures. No first-block or Fourier identity is a premise.
