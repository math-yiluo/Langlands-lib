# All-field port of `Langlands.Representation.RankinSelberg.EqualRankFactorSwapStatement`

`Langlands.AllField.Representation.RankinSelberg.EqualRankFactorSwapStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.EqualRankFactorSwapStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.EqualRankFactorSwapStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Equal-rank exchange of p-adic pair-factor certificates**

JPSS (2.12) explicitly asserts equal-rank symmetry of L and epsilon factors.
Gamma symmetry is derived from the epsilon/L-ratio formula of (3.1)(2).
This module only defines the proposition; it does not prove or assume it.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.PadicPairFactors`

## Declarations

- `Langlands.AllField.RankinSelberg.EqualRankFactorSwapStatement` (def): Equal-rank exchange for the existing L-polynomial, epsilon and gamma
  relations on actual representations of Whittaker type. Both original
  Whittaker-type hypotheses use the standard character for the same `ψ`.
  The proposition retains each relation's compatible-quotient-measure quantifiers
  and does not assert that a factor exists.
