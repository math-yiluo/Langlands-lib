# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockWhittakerDeformationStatement`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockWhittakerDeformationStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockWhittakerDeformationStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockWhittakerDeformationStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Entire Whittaker deformation for two lower-induced blocks**

The lemma of JPSS 1983, Section (4.5), printed pages 408-409, in its
inverse-character form used on page 409. For `σ_u = Ind(G_t, Q; σ_1 ⊗ α^u, σ_2)`
with `α = |det|`, every Whittaker function of `σ_0` lies in an entire family
`W_u` of Whittaker functions of `σ_u` with one compact open right stabilizer
for all `u`. The family `σ_u` is the actual canonical normalized lower
parabolic induction of the two blocks, the first twisted by
`T.determinantComplexPower (m 0 + 1) u`. This module only states the lemma.

## Imports from the port

- `Langlands.AllField.Representation.Induction.OppositeParabolic`
- `Langlands.AllField.Representation.RankinSelberg.MultiplicativityStatement`
- `Langlands.AllField.Representation.Shahidi.Induction`

## Declarations

- `Langlands.AllField.RankinSelberg.twoBlockDeformedBlocks` (abbrev): The deformed blocks `σ_u`: the first block is twisted by `|det|^u`, the
  second block is unchanged.
- `Langlands.AllField.RankinSelberg.twoBlockDeformedInduced` (abbrev): The deformed representation `ρ_u`: canonical normalized lower parabolic
  induction of the deformed blocks to `GL_(t+1)`.
- `Langlands.AllField.RankinSelberg.twoBlockDeformedBlocks_zero` (theorem): At `u = 0` the deformed blocks are the original blocks.
- `Langlands.AllField.RankinSelberg.TwoBlockWhittakerDeformationStatement` (def): JPSS 1983, Lemma of Section (4.5), printed pages 408-409, for the inverse
  character as applied on page 409. Every coefficient `g ↦ ℓ₀(ρ₀(g) v₀)` of a
  nonzero inverse-character Whittaker functional of `ρ₀` is the value at `0` of a
  family `W_u` such that each `W_u` is such a coefficient of `ρ_u`, all `W_u` are
  right invariant under one compact open subgroup, and `u ↦ W_u(g)` is entire.
