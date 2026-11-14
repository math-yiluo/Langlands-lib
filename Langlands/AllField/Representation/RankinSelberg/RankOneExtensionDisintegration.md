# All-field port of `Langlands.Representation.RankinSelberg.RankOneExtensionDisintegration`

`Langlands.AllField.Representation.RankinSelberg.RankOneExtensionDisintegration` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneExtensionDisintegration`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneExtensionDisintegration` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Lower-block disintegration at the rank of the rank-one extension**

The published lower-block chart `([g], x, h) ↦ [[[g,0],[x,h]]]` from
`N_(t+1) \ GL_(t+1) × M_(1×(t+1)) × B⁻_1` to `N_(t+2) \ GL_(t+2)`, with its target rank
written as `(1 + t) + 1`, and the specialization of `LowerBlockQuotientDisintegrationStatement`
to this chart (JPSS §9.3, printed 456, in the rank used by Lemma (5.5)).

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.LowerBlockQuotientDisintegrationStatement`
- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionAnalyticData`

## Declarations

- `Langlands.AllField.RankinSelberg.rankOneExtensionDisintegration_of_statement` (theorem): `LowerBlockQuotientDisintegrationStatement` at `n = t`, `k = 0`, with the target rank
  `t + 1 + 0 + 1` moved to `(1 + t) + 1`. The compatible measures, the additive Haar input
  and the positive scalar are those of the statement.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.rankOneExtensionQuotientChart`, `Langlands.RankinSelberg.rankOneExtensionQuotientChart_mk`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
