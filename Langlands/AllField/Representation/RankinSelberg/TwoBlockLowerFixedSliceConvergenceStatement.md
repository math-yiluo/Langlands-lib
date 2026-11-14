# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceConvergenceStatement`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceConvergenceStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceConvergenceStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceConvergenceStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Absolute convergence on every determinant slice of the Section 4.7 lower quotient**

JPSS (1983), Section 4.7, printed pages 412–414. This proposition states absolute
convergence of the actual descended lower integrand for sufficiently large opposite
real twists. The bound follows the full Whittaker-type test representation and the
supplied functionals and precedes the real parameter, quotient measure, section,
coefficient, row Schwartz function and determinant-slice integer.

Compatible standard quotient measures exist for the exact normalized group and
unipotent Haar measures. Every compatible measure and its transport by the inverse
of `[g] ↦ [Crot * g]` are sigma-finite. On each slice the proposition asserts
measurability, both absolute-integrability conclusions, and the complex and norm
integral transport identities. This is a statement, not a proof of convergence.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSliceConvergenceStatement` (def): Fixed-determinant-slice absolute convergence of the unweighted integrand in
  JPSS (4.7.1), with the supplied self-dual Fourier measure and the lower quotient
  measure transported from every compatible standard quotient measure. Full standard
  Whittaker type is assumed for the test representation and both blocks; all supplied
  functionals, including zero, and all actual coefficient-image vectors are retained.
  The single real bound may depend on the test representation and all preceding data.
