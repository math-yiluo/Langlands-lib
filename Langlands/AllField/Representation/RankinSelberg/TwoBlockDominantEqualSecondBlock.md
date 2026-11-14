# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantEqualSecondBlock`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualSecondBlock` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantEqualSecondBlock`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantEqualSecondBlock` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The actual reversed first-block law at equal rank**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantDualJacquet`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualDuality`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualFirstBlock`

## Declarations

- `Langlands.AllField.RankinSelberg.DominantRankTransport.determinantComplexPower_weylLong` (theorem): Every complex determinant power is one on the long Weyl representative.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.secondDual_oppositeTwistFunctional_val` (theorem): Dualizing a deformed block preserves the base dual functional's linear map.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.exists_equalFirstBlockBound_forOrdinaryFunctional` (theorem): The first-block bound also works for any equal block presentation and any
  functional realizing the ordinary Jacquet function.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.reversedDualSectionEquiv_ordinary` (theorem): The fixed section equivalence used by the Fourier law also realizes the
  transported second-dual functional by the ordinary reversed Jacquet integral.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.exists_reversedEqualFirstBlockBound` (theorem): Above one bound the actual reversed first-block law holds for the fixed
  transported second-dual functional, at the original real deformation parameter.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.EqualTwoSidedFirstBlockLaws` (def): The original first-block equation, the reversed first-block equation
  for the same fixed dual section, and its actual lower Fourier law.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.exists_equalTwoSidedFirstBlockLaws` (theorem): Above one real bound a nonzero ordinary Jacquet functional satisfies
  both actual first-block equations and the fixed-section lower Fourier law,
  uniformly over all three compatible quotient measures.
