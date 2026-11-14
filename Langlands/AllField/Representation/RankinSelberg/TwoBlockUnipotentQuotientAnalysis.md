# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientAnalysis`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientAnalysis` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientAnalysis`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientAnalysis` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Analytic consequences of a scaled kernel tower**

Support for the proof of `TwoBlockUnipotentQuotientIntegrationStatement` (JPSS (1983),
Section 4.6, printed pages 411-412). From a measurable s-finite kernel `κ` from
`N \ GL_(t+1)` to `H \ GL_(t+1)` whose value at `[g]_N` is the pushforward of a rectangular
measure along the radical fiber map, and from a scaled identity `κ ∘ₘ ν_N = c • ν_H` with
`0 < c < ∞`, this module derives the nonnegative Tonelli identity, the characterization of
absolute integrability, and the integrability and Bochner formula for the actual
`radicalAverage`. The kernel and the measure identity are hypotheses here.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientIntegrationStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.radicalAverage_eq_integral_kernel` (theorem): If the kernel value at every `[g]_N` is the pushforward of `μR` along the radical fiber
  map `x ↦ [u(x) g]_H`, then the actual radical average of a measurable function is its
  kernel integral at every point of `N \ GL_(t+1)`.
- `Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.analytic_of_comp_eq_smul` (theorem): The analytic conjuncts of `TwoBlockUnipotentQuotientIntegrationStatement`, for one
  restricted pair `ν_N|_s`, `ν_H|_(π⁻¹ s)`, from an s-finite kernel with the radical fiber law
  and the scaled restricted identity `κ ∘ₘ ν_N|_s = c • ν_H|_(π⁻¹ s)` with `0 < c < ∞`.
  The two restricted measures are arbitrary here; `ν_N|_s` is assumed s-finite.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.lintegral_lintegral_of_comp_eq_smul`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.integrable_iff_of_comp_eq_smul`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.integral_integral_of_comp_eq_smul`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
