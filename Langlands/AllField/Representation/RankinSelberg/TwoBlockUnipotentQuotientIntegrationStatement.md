# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientIntegrationStatement`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientIntegrationStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientIntegrationStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientIntegrationStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Normalized integration for the two-block unipotent quotient tower**

Derived analytic infrastructure for the first unfolding of JPSS (1983),
Section 4.6, printed pages 411-412. The subgroup and quotient maps are the
published actual objects. The rectangular additive Haar measure is supplied
unchanged, with its integral-cube mass retained as the factor in the measure,
Tonelli and Bochner identities. This module states, but does not prove, the
quotient-measure existence, fiber-kernel and absolute-integrability assertions.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientData`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotientIntegrationStatement` (def): Normalized integration along `H \\ G → N \\ G`, where `H` is the block-diagonal
  unipotent subgroup, for every supplied rectangular additive Haar measure.
  The factor is its positive finite integral-cube mass. The conclusions include
  compatible quotient existence, a measurable s-finite fiber kernel, restricted
  measure and Tonelli identities, and absolute-integrability and Bochner laws.
