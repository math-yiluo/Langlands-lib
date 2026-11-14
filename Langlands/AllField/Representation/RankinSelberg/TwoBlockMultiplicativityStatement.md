# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockMultiplicativityStatement`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockMultiplicativityStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockMultiplicativityStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockMultiplicativityStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Two-block multiplicativity of the factors of pairs**

The two-block cases of JPSS 1983, Theorem (3.1)(i)-(ii), printed pages 404-405.
These are the published multiplicativity targets with the number of blocks
fixed to two. Section (3.2), printed page 405, motivates isolating these cases.
The source uses lower induction; the targets use actual canonical normalized
upper induction. The required reversal, conjugation and factor transport are
future proof obligations. This module only states the two analytic targets.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.MultiplicativityStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockGammaMultiplicativityStatement` (def): JPSS Theorem (3.1)(i) with two blocks: certified gamma factors for each
  block pair exist and their product certifies the actual normalized induced pair.
  This is `GammaMultiplicativityStatement` with `k` fixed to `2`.
- `Langlands.AllField.RankinSelberg.TwoBlockLFactorMultiplicativityStatement` (def): JPSS Theorem (3.1)(ii) with two blocks: certified L-polynomials exist for
  the induced pair and both block pairs, with `X^e * ∏ i, Pi i = Q * P`.
  This is `LFactorMultiplicativityStatement` with `k` fixed to `2`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockMultiplicativityStatement`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
