# All-field port of `Langlands.Representation.RankinSelberg.EqualRankRankOneExtensionSpanComparisonStatement`

`Langlands.AllField.Representation.RankinSelberg.EqualRankRankOneExtensionSpanComparisonStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.EqualRankRankOneExtensionSpanComparisonStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.EqualRankRankOneExtensionSpanComparisonStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Equal-rank rank-one extension Laurent-span comparison**

An internal comparison for the equal-rank rank-one extension divisibility
target: every corank-one zeta value of `π × σ₁` lies in the Laurent span of
the equal-rank zeta values of `π` against the actual upper normalized
induction of `(χ, σ₁)`. It is derived from JPSS (1983), Proposition 9.1,
printed 452–454, and the last-row reduction of printed 449, displays (1)
and (3). This module only defines the proposition.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.PadicPairFactors`
- `Langlands.AllField.Representation.Shahidi.Induction`

## Declarations

- `Langlands.AllField.RankinSelberg.EqualRankRankOneExtensionSpanComparisonStatement` (def): The equal-rank rank-one extension Laurent-span comparison. For `π` on
  `GL_(t+2)` and `σ₁` on `GL_(t+1)`, both of Whittaker type, the Laurent span of
  the actual block `j = k = 0` zeta values of `π × σ₁` is contained in the
  Laurent span of the actual equal-rank zeta values of `π`, transported along
  `t + 1 = 1 + t`, against the published upper normalized induction in the
  ordered blocks `(χ, σ₁)`. This holds for all compatible quotient measures on
  both sides. Only the rank-one carrier is lifted to the universe of `σ₁`. No
  induced Whittaker-type, polynomial-existence or irreducibility premise is
  imposed.
