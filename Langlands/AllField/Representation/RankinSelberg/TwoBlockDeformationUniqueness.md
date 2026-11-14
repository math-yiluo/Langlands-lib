# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDeformationUniqueness`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationUniqueness` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDeformationUniqueness`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDeformationUniqueness` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Uniqueness of inverse-character functionals on the deformed induction**

Conditional on `NormalizedProductWhittakerTypeStatement` (normalized upper block
induction preserves full standard Whittaker type), the deformed lower induction
`ρ_u = Ind(G_t, Q̄; σ_1 ⊗ α^u, σ_2)` has full inverse-standard Whittaker type for
every complex `u`. Hence any two inverse-character functionals on `ρ_u` are
proportional when the first is nonzero. Each block of full standard type also has
a nonzero inverse-character functional.

## Imports from the port

- `Langlands.AllField.Representation.Induction.OppositeProductReversalProof`
- `Langlands.AllField.Representation.RankinSelberg.NormalizedProductWhittakerTypeStatement`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockWhittakerDeformationStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.twoBlockDeformedBlocks_isOfWhittakerType_iff` (theorem): A deformed block has full Whittaker type for a character exactly when the
  original block does: the twist `|det|^u` has open kernel and is trivial on the
  upper unipotent subgroup.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.exists_block_inverse_functional` (theorem): Every block of full standard Whittaker type has a nonzero inverse-character
  functional.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.deformedBlockFunctional` (def): An inverse-character functional of the block `σ i` is, with the same linear map,
  an inverse-character functional of the deformed block at every `u`, because
  `|det|^u` is trivial on the upper unipotent subgroup.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.deformedBlockFunctional_val` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.isOfWhittakerType_twoBlockDeformedInduced` (theorem): Conditional on `NormalizedProductWhittakerTypeStatement`, the deformed lower
  induction `ρ_u` has full inverse-standard Whittaker type for every complex `u`. It is
  equivalent to the upper normalized induction of the reversed deformed blocks.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.functional_eq_smul` (theorem): Conditional on `NormalizedProductWhittakerTypeStatement`, every inverse-character
  functional on `ρ_u` is a multiple of any nonzero one.
