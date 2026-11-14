# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankModelImageStatement`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelImageStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankModelImageStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankModelImageStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Large-second-twist image equality for the JPSS adjacent-rank model**

The literal Section 6.1 integral has, for all sufficiently large real twists
of the second lower block, the same image as the coefficients of one nonzero
Whittaker functional on the actual normalized opposite parabolic induction.
This module defines an unproved, source-derived proposition.

## Imports from the port

- `Langlands.AllField.Representation.Induction.OppositeParabolic`
- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankIntegralModel`
- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionCharacter`
- `Langlands.AllField.Representation.Shahidi.Induction`

## Declarations

- `Langlands.AllField.RankinSelberg.AdjacentRankModelImageStatement` (def): The large-positive-second-twist image assertion of JPSS Section 6.1,
  formula (8), retaining the original full Whittaker-type representation as
  the first inducing block. The bound is uniform over all test tensors, and
  the same nonzero induced functional supplies every coefficient in the image.
  This is a proposition definition, with the original-carrier transport and
  the analytic and spanning arguments left to a later proof.
