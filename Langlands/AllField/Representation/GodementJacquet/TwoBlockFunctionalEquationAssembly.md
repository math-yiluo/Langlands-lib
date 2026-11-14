# All-field port of `Langlands.Representation.GodementJacquet.TwoBlockFunctionalEquationAssembly`

`Langlands.AllField.Representation.GodementJacquet.TwoBlockFunctionalEquationAssembly` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.TwoBlockFunctionalEquationAssembly`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.TwoBlockFunctionalEquationAssembly` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Assembly of the two-block normalized functional equation**

The closed two-block functional-equation statement follows from the two-block
analytic statement and a matched expansion of the induced zeta integral and its
transformed integral into finite sums of products of block zeta integrals with the
same block data. See the paired Markdown.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.TwoBlockMatrixAnalyticInductionStatement`
- `Langlands.AllField.Representation.GodementJacquet.TwoBlockMatrixFunctionalEquationInductionStatement`

## Declarations

- `Langlands.AllField.GodementJacquet.TwoBlockMatchedZetaExpansionStatement` (def): Matched expansion of induced zeta integrals (internal interface). Under the
  hypotheses of the two-block functional-equation statement, for every full-matrix
  test `Φ` and every coefficient `f = ⟨ℓ, I(g) v⟩` of a smooth functional and a smooth
  vector of the normalized induced representation `I` there are finitely many block
  tests `Ψ0 j`, `Ψ1 j` and block coefficients `f0 j`, `f1 j` such that, on a right
  half-plane, `Z(Φ, s + t/2, f) = ∑ j, Z(Ψ0 j, s + m0/2, f0 j) Z(Ψ1 j, s + m1/2, f1 j)`,
  and, on a right half-plane, the same identity holds for the full Fourier transforms
  of the tests and the inverse-transpose transforms of the same coefficients.
- `Langlands.AllField.GodementJacquet.twoBlockMatrixFunctionalEquationInduction_of_expansion` (theorem): The two-block functional-equation statement follows from the two-block analytic
  statement and the matched expansion.
