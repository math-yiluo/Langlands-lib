# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientIntegrationStatement`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientIntegrationStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientIntegrationStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientIntegrationStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Linked lower mixed quotient integration in JPSS Section 4.9**

The measure disintegrations underlying equations (2) and (8), printed pages
416 and 418, share a Haar measure on the actual lower mixed subgroup, normalized
on its integral points. Every supplied rectangular Haar measure is retained:
its integral-cube mass occurs in equation (2). Equation (8) has the positive
density `|det v|^b`, constant on each small determinant slice, and no cube factor.
Kernel, normalization and absolute-integrability packaging are derived content.
This module states these assertions; it does not prove them.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotientIntegrationStatement` (def): The two actual lower mixed quotient disintegrations of JPSS Section 4.9,
  with one mass-one lower mixed Haar measure, compatible quotient existence and
  transport from the full-unipotent quotient, measurable s-finite kernels, Tonelli,
  absolute-integrability equivalences, and the Bochner laws for the published
  unweighted descended averages.
