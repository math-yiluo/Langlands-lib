# All-field port of `Langlands.Representation.RankinSelberg.RankOneExtensionSpanComparisonStatement`

`Langlands.AllField.Representation.RankinSelberg.RankOneExtensionSpanComparisonStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneExtensionSpanComparisonStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneExtensionSpanComparisonStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Strict rank-one extension Laurent-span comparison**

JPSS (1983), Lemma (5.5), printed 423–427: in the strict rank range, every
block-one zeta value of `π × σ₁` lies in the Laurent span of the block-zero
zeta values of `π` against the actual lower induction `(σ₁, χ)`. This module
only defines the proposition.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionTransport`

## Declarations

- `Langlands.AllField.RankinSelberg.RankOneExtensionSpanComparisonStatement` (def): The early JPSS Lemma (5.5) comparison in its original strict rank range
  `t + 3 ≤ r + 1`. The Laurent span of the actual block-one zeta values of
  `π × σ₁`, with predecessor rank `t`, is contained in the Laurent span of the
  actual block-zero zeta values of `π` against the published lower induction of
  `(σ₁, χ)`, with predecessor rank `1 + t`. Both sides have the same trailing
  index `r - t - 2`. Only the rank-one carrier is lifted to the universe of `σ₁`.
  No induced Whittaker-type, polynomial-existence or irreducibility premise is
  imposed.
