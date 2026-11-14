# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientAnalysis`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockQuotientAnalysis` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientAnalysis`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientAnalysis` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Analytic consequences of first-block quotient disintegration**

From the everywhere representative formula for a measurable fiber kernel and its exact
restricted-measure composition identity, derive the Tonelli, absolute-integrability and
Bochner conclusions for the published first-block average. The kernel and the normalized
composition identity are hypotheses of this helper, not conclusions.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockQuotientIntegrationStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockAverage_eq_integral_kernel` (theorem): The published first-block average agrees everywhere with integration against any kernel
  having the prescribed representative formula. No integrability assumption is needed.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.FirstBlockKernelAnalysisStatement` (def): All analytic conclusions of first-block quotient disintegration for a fixed slice follow
  from the exact kernel formula and `κ ∘ₘ νL0 = νHk`. The two base measures may be arbitrary;
  for the target theorem they are the zero outer slice and the k-th total slice.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.analytic_of_comp_eq` (theorem): The conditional analytic statement follows from the representative formula and exact
  measure composition, using the general integration theorems for measurable kernels.
