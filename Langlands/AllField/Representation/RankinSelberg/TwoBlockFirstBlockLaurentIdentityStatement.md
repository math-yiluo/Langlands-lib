# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIdentityStatement`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIdentityStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIdentityStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIdentityStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The polynomial-cleared first-block JPSS Laurent identity**

JPSS (1983), Section 4.7 equation (1), printed page 412, and the first-block
functional-equation calculation in Section 4.9, printed pages 416–418.
This module states the identity in the module of bilateral coefficient functions
under finite Laurent convolution, retaining the actual normalized generators.
Convergence is unconditional in the small-block epsilon certificate. The common
epsilon witnesses precede all sections, coefficient vectors and Schwartz tests.
No analytic proof or cancellation of polynomial factors is supplied here.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockUnfoldingIntegrandData`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurentIdentityStatement` (def): The coefficientwise, polynomial-cleared first-block identity of JPSS (4.7.1).
  The total test rank is `t + 1`, the blocks have sizes `m 0 + 1` and `m 1 + 1`,
  and the single bound follows every representation and supplied functional.
  For every compatible pair of the normalized quotient measures, all coefficients
  are absolutely integrable; a supplied first-block epsilon equation then has
  common normalized-generator witnesses giving the finite Laurent identity.
